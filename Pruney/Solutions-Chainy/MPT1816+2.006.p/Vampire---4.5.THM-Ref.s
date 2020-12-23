%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:45 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  248 (2076 expanded)
%              Number of leaves         :   46 ( 494 expanded)
%              Depth                    :   19
%              Number of atoms          : 1100 (34511 expanded)
%              Number of equality atoms :   29 (1414 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f103,f115,f117,f128,f271,f297,f310,f328,f334,f340,f344,f350,f357,f359,f365,f372,f391,f517,f519,f523,f778,f794,f795,f850,f867,f869,f871,f914,f926,f996,f1023,f1025,f1027,f1111,f1114,f1300])).

fof(f1300,plain,
    ( ~ spl7_2
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f1298])).

fof(f1298,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(resolution,[],[f149,f96])).

fof(f96,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_2
  <=> sP5(sK4,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f149,plain,
    ( ! [X0] : ~ sP5(sK4,X0,sK2,sK1,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl7_8
  <=> ! [X0] : ~ sP5(sK4,X0,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1114,plain,
    ( ~ spl7_2
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f1113])).

fof(f1113,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(resolution,[],[f984,f96])).

fof(f984,plain,
    ( ! [X0] : ~ sP5(X0,sK3,sK2,sK1,sK0)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f983])).

fof(f983,plain,
    ( spl7_58
  <=> ! [X0] : ~ sP5(X0,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f1111,plain,
    ( ~ spl7_60
    | ~ spl7_61
    | ~ spl7_62
    | ~ spl7_42
    | ~ spl7_43
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_59
    | spl7_34 ),
    inference(avatar_split_clause,[],[f1104,f506,f986,f845,f841,f837,f833,f998,f994,f990])).

fof(f990,plain,
    ( spl7_60
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f994,plain,
    ( spl7_61
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f998,plain,
    ( spl7_62
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f833,plain,
    ( spl7_42
  <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f837,plain,
    ( spl7_43
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f841,plain,
    ( spl7_44
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f845,plain,
    ( spl7_45
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f986,plain,
    ( spl7_59
  <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f506,plain,
    ( spl7_34
  <=> sP6(sK2,sK4,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1104,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1103,f197])).

fof(f197,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(resolution,[],[f192,f53])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f54,f57,f58,f59,f60,f61,f62,f55,f191])).

fof(f191,plain,(
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
    inference(forward_demodulation,[],[f180,f142])).

fof(f142,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ),
    inference(global_subsumption,[],[f54,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f89,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f180,plain,(
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
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f55,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f1103,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1102,f196])).

fof(f196,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(resolution,[],[f192,f49])).

fof(f49,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1102,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1101,f196])).

fof(f1101,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1100,f196])).

fof(f1100,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1099,f196])).

fof(f1099,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1098,f197])).

fof(f1098,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1097,f197])).

fof(f1097,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(forward_demodulation,[],[f1096,f197])).

fof(f1096,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_34 ),
    inference(resolution,[],[f925,f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f925,plain,
    ( ~ sP6(sK2,sK4,sK3,sK1,sK0)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f506])).

fof(f1027,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_28
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1026,f998,f295,f283,f280])).

fof(f280,plain,
    ( spl7_23
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f283,plain,
    ( spl7_24
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f295,plain,
    ( spl7_28
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f1026,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f54,f55,f56,f965])).

fof(f965,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f88,f197])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1025,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_28
    | spl7_60 ),
    inference(avatar_split_clause,[],[f1024,f990,f295,f283,f280])).

fof(f1024,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f54,f55,f56,f964])).

fof(f964,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f87,f197])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1023,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_28
    | spl7_59 ),
    inference(avatar_split_clause,[],[f1022,f986,f295,f283,f280])).

fof(f1022,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f54,f55,f56,f963])).

fof(f963,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f86,f197])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f996,plain,
    ( spl7_58
    | spl7_61 ),
    inference(avatar_split_clause,[],[f949,f994,f983])).

fof(f949,plain,(
    ! [X2] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
      | ~ sP5(X2,sK3,sK2,sK1,sK0) ) ),
    inference(superposition,[],[f37,f197])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f926,plain,
    ( ~ spl7_34
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_35
    | ~ spl7_36
    | spl7_37
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f418,f125,f92,f515,f512,f509,f292,f289,f286,f506])).

fof(f286,plain,
    ( spl7_25
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f289,plain,
    ( spl7_26
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f292,plain,
    ( spl7_27
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f509,plain,
    ( spl7_35
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f512,plain,
    ( spl7_36
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f515,plain,
    ( spl7_37
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f92,plain,
    ( spl7_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f125,plain,
    ( spl7_5
  <=> sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f418,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ spl7_5 ),
    inference(superposition,[],[f273,f200])).

fof(f200,plain,
    ( sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f198,f126])).

fof(f126,plain,
    ( sK2 = k7_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f198,plain,(
    k7_relat_1(sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(resolution,[],[f192,f170])).

fof(f170,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(global_subsumption,[],[f48,f52,f60,f62,f49,f53,f168])).

fof(f168,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f85,f50])).

fof(f50,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
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

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f273,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ sP6(X1,sK4,sK3,X0,sK0) ) ),
    inference(global_subsumption,[],[f48,f52,f60,f61,f62,f49,f53,f51,f272])).

fof(f272,plain,(
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
    inference(superposition,[],[f78,f50])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    r4_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f914,plain,(
    ~ spl7_37 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl7_37 ),
    inference(resolution,[],[f516,f57])).

fof(f516,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f515])).

fof(f871,plain,
    ( ~ spl7_23
    | ~ spl7_29
    | ~ spl7_28
    | spl7_45 ),
    inference(avatar_split_clause,[],[f870,f845,f295,f342,f280])).

fof(f342,plain,
    ( spl7_29
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f870,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f54,f55,f56,f815])).

fof(f815,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f88,f196])).

fof(f869,plain,
    ( ~ spl7_23
    | ~ spl7_29
    | ~ spl7_28
    | spl7_43 ),
    inference(avatar_split_clause,[],[f868,f837,f295,f342,f280])).

fof(f868,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f54,f55,f56,f814])).

fof(f814,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f87,f196])).

fof(f867,plain,
    ( ~ spl7_23
    | ~ spl7_29
    | ~ spl7_28
    | spl7_42 ),
    inference(avatar_split_clause,[],[f866,f833,f295,f342,f280])).

fof(f866,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f54,f55,f56,f813])).

fof(f813,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f86,f196])).

fof(f850,plain,
    ( spl7_8
    | spl7_44 ),
    inference(avatar_split_clause,[],[f803,f841,f148])).

fof(f803,plain,(
    ! [X6] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
      | ~ sP5(sK4,X6,sK2,sK1,sK0) ) ),
    inference(superposition,[],[f41,f196])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f795,plain,
    ( spl7_17
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | spl7_17
    | ~ spl7_34 ),
    inference(resolution,[],[f507,f329])).

fof(f329,plain,
    ( ! [X0] : ~ sP6(sK2,sK4,X0,sK1,sK0)
    | spl7_17 ),
    inference(resolution,[],[f255,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f255,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl7_17
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f507,plain,
    ( sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f506])).

fof(f794,plain,
    ( spl7_21
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | spl7_21
    | ~ spl7_34 ),
    inference(resolution,[],[f507,f336])).

fof(f336,plain,
    ( ! [X1] : ~ sP6(sK2,X1,sK3,sK1,sK0)
    | spl7_21 ),
    inference(resolution,[],[f267,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f267,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl7_21
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f778,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f287,f56])).

fof(f287,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f286])).

fof(f523,plain,(
    spl7_36 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl7_36 ),
    inference(resolution,[],[f513,f58])).

fof(f513,plain,
    ( ~ v2_pre_topc(sK1)
    | spl7_36 ),
    inference(avatar_component_clause,[],[f512])).

fof(f519,plain,(
    spl7_35 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl7_35 ),
    inference(resolution,[],[f510,f59])).

fof(f510,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_35 ),
    inference(avatar_component_clause,[],[f509])).

fof(f517,plain,
    ( ~ spl7_1
    | spl7_34
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_35
    | ~ spl7_36
    | spl7_37
    | ~ spl7_25
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f498,f125,f286,f515,f512,f509,f292,f289,f506,f92])).

fof(f498,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,
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
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_5 ),
    inference(superposition,[],[f320,f200])).

fof(f320,plain,(
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
    inference(global_subsumption,[],[f48,f52,f60,f61,f62,f49,f53,f51,f317])).

fof(f317,plain,(
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
    inference(superposition,[],[f75,f50])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f391,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f290,f55])).

fof(f290,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f289])).

fof(f372,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_20 ),
    inference(avatar_split_clause,[],[f367,f263,f295,f292,f289,f286,f283,f280])).

fof(f263,plain,
    ( spl7_20
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f367,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_20 ),
    inference(resolution,[],[f264,f88])).

fof(f264,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f263])).

fof(f365,plain,
    ( ~ spl7_23
    | ~ spl7_29
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_16 ),
    inference(avatar_split_clause,[],[f360,f251,f295,f292,f289,f286,f342,f280])).

fof(f251,plain,
    ( spl7_16
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f360,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | spl7_16 ),
    inference(resolution,[],[f252,f88])).

fof(f252,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f359,plain,(
    spl7_29 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl7_29 ),
    inference(resolution,[],[f351,f106])).

fof(f106,plain,(
    l1_pre_topc(sK4) ),
    inference(global_subsumption,[],[f62,f104])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f351,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_29 ),
    inference(resolution,[],[f343,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f343,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f342])).

fof(f357,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_22 ),
    inference(avatar_split_clause,[],[f352,f269,f295,f292,f289,f286,f283,f280])).

fof(f269,plain,
    ( spl7_22
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f352,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_22 ),
    inference(resolution,[],[f270,f87])).

fof(f270,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f269])).

fof(f350,plain,
    ( ~ spl7_23
    | ~ spl7_29
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_18 ),
    inference(avatar_split_clause,[],[f345,f257,f295,f292,f289,f286,f342,f280])).

fof(f257,plain,
    ( spl7_18
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f345,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | spl7_18 ),
    inference(resolution,[],[f258,f87])).

fof(f258,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f257])).

fof(f344,plain,
    ( ~ spl7_23
    | ~ spl7_29
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_19 ),
    inference(avatar_split_clause,[],[f322,f260,f295,f292,f289,f286,f342,f280])).

fof(f260,plain,
    ( spl7_19
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f322,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | spl7_19 ),
    inference(resolution,[],[f261,f86])).

fof(f261,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f260])).

fof(f340,plain,(
    spl7_28 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl7_28 ),
    inference(resolution,[],[f321,f59])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_28 ),
    inference(resolution,[],[f296,f64])).

fof(f296,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f295])).

fof(f334,plain,(
    spl7_24 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl7_24 ),
    inference(resolution,[],[f308,f107])).

fof(f107,plain,(
    l1_pre_topc(sK3) ),
    inference(global_subsumption,[],[f62,f105])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f65,f53])).

fof(f308,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_24 ),
    inference(resolution,[],[f284,f64])).

fof(f284,plain,
    ( ~ l1_struct_0(sK3)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f283])).

fof(f328,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl7_23 ),
    inference(resolution,[],[f300,f62])).

fof(f300,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_23 ),
    inference(resolution,[],[f281,f64])).

fof(f281,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f280])).

fof(f310,plain,(
    spl7_27 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl7_27 ),
    inference(resolution,[],[f293,f54])).

fof(f293,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f292])).

fof(f297,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_15 ),
    inference(avatar_split_clause,[],[f274,f248,f295,f292,f289,f286,f283,f280])).

fof(f248,plain,
    ( spl7_15
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f274,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_15 ),
    inference(resolution,[],[f249,f86])).

fof(f249,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f271,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22
    | spl7_2 ),
    inference(avatar_split_clause,[],[f246,f95,f269,f266,f263,f260,f257,f254,f251,f248])).

fof(f246,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(resolution,[],[f102,f34])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f128,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f123,f110,f125])).

fof(f110,plain,
    ( spl7_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f120,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f120,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f114,f81])).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f114,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_4
  <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f115,plain,
    ( spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f108,f113,f110])).

fof(f108,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f103,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f100,f95,f92])).

fof(f100,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f90,f98,f99,f43])).

fof(f43,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f99,plain,(
    v1_funct_1(sK2) ),
    inference(global_subsumption,[],[f54])).

fof(f98,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f55])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(global_subsumption,[],[f56])).

fof(f97,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f46,f95,f92])).

fof(f46,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (19800)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.43  % (19808)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.49  % (19803)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (19810)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (19809)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (19813)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (19794)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (19791)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (19796)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (19793)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (19794)Refutation not found, incomplete strategy% (19794)------------------------------
% 0.21/0.50  % (19794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19794)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19794)Memory used [KB]: 10746
% 0.21/0.50  % (19794)Time elapsed: 0.099 s
% 0.21/0.50  % (19794)------------------------------
% 0.21/0.50  % (19794)------------------------------
% 0.21/0.50  % (19795)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (19797)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (19802)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (19798)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (19798)Refutation not found, incomplete strategy% (19798)------------------------------
% 0.21/0.51  % (19798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19798)Memory used [KB]: 6268
% 0.21/0.51  % (19798)Time elapsed: 0.108 s
% 0.21/0.51  % (19798)------------------------------
% 0.21/0.51  % (19798)------------------------------
% 0.21/0.51  % (19804)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.26/0.51  % (19801)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.26/0.52  % (19806)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.26/0.52  % (19814)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.26/0.52  % (19812)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.26/0.52  % (19811)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.26/0.52  % (19814)Refutation not found, incomplete strategy% (19814)------------------------------
% 1.26/0.52  % (19814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (19792)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.26/0.53  % (19814)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (19814)Memory used [KB]: 10746
% 1.26/0.53  % (19814)Time elapsed: 0.116 s
% 1.26/0.53  % (19814)------------------------------
% 1.26/0.53  % (19814)------------------------------
% 1.50/0.54  % (19805)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.50/0.54  % (19799)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.50/0.55  % (19807)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.50/0.57  % (19801)Refutation not found, incomplete strategy% (19801)------------------------------
% 1.50/0.57  % (19801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (19801)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (19801)Memory used [KB]: 11129
% 1.50/0.57  % (19801)Time elapsed: 0.142 s
% 1.50/0.57  % (19801)------------------------------
% 1.50/0.57  % (19801)------------------------------
% 1.50/0.57  % (19799)Refutation not found, incomplete strategy% (19799)------------------------------
% 1.50/0.57  % (19799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (19799)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (19799)Memory used [KB]: 11385
% 1.50/0.57  % (19799)Time elapsed: 0.155 s
% 1.50/0.57  % (19799)------------------------------
% 1.50/0.57  % (19799)------------------------------
% 1.50/0.58  % (19807)Refutation not found, incomplete strategy% (19807)------------------------------
% 1.50/0.58  % (19807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (19807)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (19807)Memory used [KB]: 2302
% 1.50/0.58  % (19807)Time elapsed: 0.163 s
% 1.50/0.58  % (19807)------------------------------
% 1.50/0.58  % (19807)------------------------------
% 1.50/0.61  % (19813)Refutation not found, incomplete strategy% (19813)------------------------------
% 1.50/0.61  % (19813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (19813)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.61  
% 1.50/0.61  % (19813)Memory used [KB]: 1791
% 1.50/0.61  % (19813)Time elapsed: 0.156 s
% 1.50/0.61  % (19813)------------------------------
% 1.50/0.61  % (19813)------------------------------
% 1.50/0.64  % (19803)Refutation found. Thanks to Tanya!
% 1.50/0.64  % SZS status Theorem for theBenchmark
% 2.27/0.64  % SZS output start Proof for theBenchmark
% 2.27/0.64  fof(f1305,plain,(
% 2.27/0.64    $false),
% 2.27/0.64    inference(avatar_sat_refutation,[],[f97,f103,f115,f117,f128,f271,f297,f310,f328,f334,f340,f344,f350,f357,f359,f365,f372,f391,f517,f519,f523,f778,f794,f795,f850,f867,f869,f871,f914,f926,f996,f1023,f1025,f1027,f1111,f1114,f1300])).
% 2.27/0.64  fof(f1300,plain,(
% 2.27/0.64    ~spl7_2 | ~spl7_8),
% 2.27/0.64    inference(avatar_contradiction_clause,[],[f1298])).
% 2.27/0.64  fof(f1298,plain,(
% 2.27/0.64    $false | (~spl7_2 | ~spl7_8)),
% 2.27/0.64    inference(resolution,[],[f149,f96])).
% 2.27/0.64  fof(f96,plain,(
% 2.27/0.64    sP5(sK4,sK3,sK2,sK1,sK0) | ~spl7_2),
% 2.27/0.64    inference(avatar_component_clause,[],[f95])).
% 2.27/0.64  fof(f95,plain,(
% 2.27/0.64    spl7_2 <=> sP5(sK4,sK3,sK2,sK1,sK0)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.27/0.64  fof(f149,plain,(
% 2.27/0.64    ( ! [X0] : (~sP5(sK4,X0,sK2,sK1,sK0)) ) | ~spl7_8),
% 2.27/0.64    inference(avatar_component_clause,[],[f148])).
% 2.27/0.64  fof(f148,plain,(
% 2.27/0.64    spl7_8 <=> ! [X0] : ~sP5(sK4,X0,sK2,sK1,sK0)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.27/0.64  fof(f1114,plain,(
% 2.27/0.64    ~spl7_2 | ~spl7_58),
% 2.27/0.64    inference(avatar_contradiction_clause,[],[f1113])).
% 2.27/0.64  fof(f1113,plain,(
% 2.27/0.64    $false | (~spl7_2 | ~spl7_58)),
% 2.27/0.64    inference(resolution,[],[f984,f96])).
% 2.27/0.64  fof(f984,plain,(
% 2.27/0.64    ( ! [X0] : (~sP5(X0,sK3,sK2,sK1,sK0)) ) | ~spl7_58),
% 2.27/0.64    inference(avatar_component_clause,[],[f983])).
% 2.27/0.64  fof(f983,plain,(
% 2.27/0.64    spl7_58 <=> ! [X0] : ~sP5(X0,sK3,sK2,sK1,sK0)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 2.27/0.64  fof(f1111,plain,(
% 2.27/0.64    ~spl7_60 | ~spl7_61 | ~spl7_62 | ~spl7_42 | ~spl7_43 | ~spl7_44 | ~spl7_45 | ~spl7_59 | spl7_34),
% 2.27/0.64    inference(avatar_split_clause,[],[f1104,f506,f986,f845,f841,f837,f833,f998,f994,f990])).
% 2.27/0.64  fof(f990,plain,(
% 2.27/0.64    spl7_60 <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 2.27/0.64  fof(f994,plain,(
% 2.27/0.64    spl7_61 <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 2.27/0.64  fof(f998,plain,(
% 2.27/0.64    spl7_62 <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 2.27/0.64  fof(f833,plain,(
% 2.27/0.64    spl7_42 <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.27/0.64  fof(f837,plain,(
% 2.27/0.64    spl7_43 <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.27/0.64  fof(f841,plain,(
% 2.27/0.64    spl7_44 <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.27/0.64  fof(f845,plain,(
% 2.27/0.64    spl7_45 <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.27/0.64  fof(f986,plain,(
% 2.27/0.64    spl7_59 <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 2.27/0.64  fof(f506,plain,(
% 2.27/0.64    spl7_34 <=> sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.27/0.64  fof(f1104,plain,(
% 2.27/0.64    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1103,f197])).
% 2.27/0.64  fof(f197,plain,(
% 2.27/0.64    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))),
% 2.27/0.64    inference(resolution,[],[f192,f53])).
% 2.27/0.64  fof(f53,plain,(
% 2.27/0.64    m1_pre_topc(sK3,sK0)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f17,plain,(
% 2.27/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/0.64    inference(flattening,[],[f16])).
% 2.27/0.64  fof(f16,plain,(
% 2.27/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.27/0.64    inference(ennf_transformation,[],[f13])).
% 2.27/0.64  fof(f13,negated_conjecture,(
% 2.27/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.27/0.64    inference(negated_conjecture,[],[f12])).
% 2.27/0.64  fof(f12,conjecture,(
% 2.27/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.27/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).
% 2.27/0.64  fof(f192,plain,(
% 2.27/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0))) )),
% 2.27/0.64    inference(global_subsumption,[],[f54,f57,f58,f59,f60,f61,f62,f55,f191])).
% 2.27/0.64  fof(f191,plain,(
% 2.27/0.64    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.27/0.64    inference(forward_demodulation,[],[f180,f142])).
% 2.27/0.64  fof(f142,plain,(
% 2.27/0.64    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 2.27/0.64    inference(global_subsumption,[],[f54,f139])).
% 2.27/0.64  fof(f139,plain,(
% 2.27/0.64    ( ! [X0] : (~v1_funct_1(sK2) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 2.27/0.64    inference(resolution,[],[f89,f56])).
% 2.27/0.64  fof(f56,plain,(
% 2.27/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f89,plain,(
% 2.27/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f33])).
% 2.27/0.64  fof(f33,plain,(
% 2.27/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.27/0.64    inference(flattening,[],[f32])).
% 2.27/0.64  fof(f32,plain,(
% 2.27/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.27/0.64    inference(ennf_transformation,[],[f5])).
% 2.27/0.64  fof(f5,axiom,(
% 2.27/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.27/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.27/0.64  fof(f180,plain,(
% 2.27/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 2.27/0.64    inference(resolution,[],[f80,f56])).
% 2.27/0.64  fof(f80,plain,(
% 2.27/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.27/0.64    inference(cnf_transformation,[],[f24])).
% 2.27/0.64  fof(f24,plain,(
% 2.27/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.64    inference(flattening,[],[f23])).
% 2.27/0.64  fof(f23,plain,(
% 2.27/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.64    inference(ennf_transformation,[],[f8])).
% 2.27/0.64  fof(f8,axiom,(
% 2.27/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.27/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.27/0.64  fof(f55,plain,(
% 2.27/0.64    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f62,plain,(
% 2.27/0.64    l1_pre_topc(sK0)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f61,plain,(
% 2.27/0.64    v2_pre_topc(sK0)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f60,plain,(
% 2.27/0.64    ~v2_struct_0(sK0)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f59,plain,(
% 2.27/0.64    l1_pre_topc(sK1)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f58,plain,(
% 2.27/0.64    v2_pre_topc(sK1)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f57,plain,(
% 2.27/0.64    ~v2_struct_0(sK1)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f54,plain,(
% 2.27/0.64    v1_funct_1(sK2)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f1103,plain,(
% 2.27/0.64    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1102,f196])).
% 2.27/0.64  fof(f196,plain,(
% 2.27/0.64    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))),
% 2.27/0.64    inference(resolution,[],[f192,f49])).
% 2.27/0.64  fof(f49,plain,(
% 2.27/0.64    m1_pre_topc(sK4,sK0)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f1102,plain,(
% 2.27/0.64    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1101,f196])).
% 2.27/0.64  fof(f1101,plain,(
% 2.27/0.64    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1100,f196])).
% 2.27/0.64  fof(f1100,plain,(
% 2.27/0.64    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1099,f196])).
% 2.27/0.64  fof(f1099,plain,(
% 2.27/0.64    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1098,f197])).
% 2.27/0.64  fof(f1098,plain,(
% 2.27/0.64    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1097,f197])).
% 2.27/0.64  fof(f1097,plain,(
% 2.27/0.64    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(forward_demodulation,[],[f1096,f197])).
% 2.27/0.64  fof(f1096,plain,(
% 2.27/0.64    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_34),
% 2.27/0.64    inference(resolution,[],[f925,f66])).
% 2.27/0.64  fof(f66,plain,(
% 2.27/0.64    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X3,X2,X1,X0) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) )),
% 2.27/0.64    inference(cnf_transformation,[],[f22])).
% 2.27/0.64  fof(f22,plain,(
% 2.27/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.64    inference(flattening,[],[f21])).
% 2.27/0.64  fof(f21,plain,(
% 2.27/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.64    inference(ennf_transformation,[],[f11])).
% 2.27/0.64  fof(f11,axiom,(
% 2.27/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 2.27/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).
% 2.27/0.64  fof(f925,plain,(
% 2.27/0.64    ~sP6(sK2,sK4,sK3,sK1,sK0) | spl7_34),
% 2.27/0.64    inference(avatar_component_clause,[],[f506])).
% 2.27/0.64  fof(f1027,plain,(
% 2.27/0.64    ~spl7_23 | ~spl7_24 | ~spl7_28 | spl7_62),
% 2.27/0.64    inference(avatar_split_clause,[],[f1026,f998,f295,f283,f280])).
% 2.27/0.64  fof(f280,plain,(
% 2.27/0.64    spl7_23 <=> l1_struct_0(sK0)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.27/0.64  fof(f283,plain,(
% 2.27/0.64    spl7_24 <=> l1_struct_0(sK3)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.27/0.64  fof(f295,plain,(
% 2.27/0.64    spl7_28 <=> l1_struct_0(sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.27/0.64  fof(f1026,plain,(
% 2.27/0.64    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.27/0.64    inference(global_subsumption,[],[f54,f55,f56,f965])).
% 2.27/0.64  fof(f965,plain,(
% 2.27/0.64    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.27/0.64    inference(superposition,[],[f88,f197])).
% 2.27/0.64  fof(f88,plain,(
% 2.27/0.64    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f31])).
% 2.27/0.64  fof(f31,plain,(
% 2.27/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.27/0.64    inference(flattening,[],[f30])).
% 2.27/0.64  fof(f30,plain,(
% 2.27/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.27/0.64    inference(ennf_transformation,[],[f10])).
% 2.27/0.64  fof(f10,axiom,(
% 2.27/0.64    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.27/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 2.27/0.64  fof(f1025,plain,(
% 2.27/0.64    ~spl7_23 | ~spl7_24 | ~spl7_28 | spl7_60),
% 2.27/0.64    inference(avatar_split_clause,[],[f1024,f990,f295,f283,f280])).
% 2.27/0.64  fof(f1024,plain,(
% 2.27/0.64    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.27/0.64    inference(global_subsumption,[],[f54,f55,f56,f964])).
% 2.27/0.64  fof(f964,plain,(
% 2.27/0.64    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.27/0.64    inference(superposition,[],[f87,f197])).
% 2.27/0.64  fof(f87,plain,(
% 2.27/0.64    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f31])).
% 2.27/0.64  fof(f1023,plain,(
% 2.27/0.64    ~spl7_23 | ~spl7_24 | ~spl7_28 | spl7_59),
% 2.27/0.64    inference(avatar_split_clause,[],[f1022,f986,f295,f283,f280])).
% 2.27/0.64  fof(f1022,plain,(
% 2.27/0.64    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.27/0.64    inference(global_subsumption,[],[f54,f55,f56,f963])).
% 2.27/0.64  fof(f963,plain,(
% 2.27/0.64    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.27/0.64    inference(superposition,[],[f86,f197])).
% 2.27/0.64  fof(f86,plain,(
% 2.27/0.64    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f31])).
% 2.27/0.64  fof(f996,plain,(
% 2.27/0.64    spl7_58 | spl7_61),
% 2.27/0.64    inference(avatar_split_clause,[],[f949,f994,f983])).
% 2.27/0.64  fof(f949,plain,(
% 2.27/0.64    ( ! [X2] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~sP5(X2,sK3,sK2,sK1,sK0)) )),
% 2.27/0.64    inference(superposition,[],[f37,f197])).
% 2.27/0.64  fof(f37,plain,(
% 2.27/0.64    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~sP5(X4,X3,X2,X1,X0)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f926,plain,(
% 2.27/0.64    ~spl7_34 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_35 | ~spl7_36 | spl7_37 | spl7_1 | ~spl7_5),
% 2.27/0.64    inference(avatar_split_clause,[],[f418,f125,f92,f515,f512,f509,f292,f289,f286,f506])).
% 2.27/0.64  fof(f286,plain,(
% 2.27/0.64    spl7_25 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.27/0.64  fof(f289,plain,(
% 2.27/0.64    spl7_26 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.27/0.64  fof(f292,plain,(
% 2.27/0.64    spl7_27 <=> v1_funct_1(sK2)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 2.27/0.64  fof(f509,plain,(
% 2.27/0.64    spl7_35 <=> l1_pre_topc(sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.27/0.64  fof(f512,plain,(
% 2.27/0.64    spl7_36 <=> v2_pre_topc(sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.27/0.64  fof(f515,plain,(
% 2.27/0.64    spl7_37 <=> v2_struct_0(sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 2.27/0.64  fof(f92,plain,(
% 2.27/0.64    spl7_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.27/0.64  fof(f125,plain,(
% 2.27/0.64    spl7_5 <=> sK2 = k7_relat_1(sK2,u1_struct_0(sK0))),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.27/0.64  fof(f418,plain,(
% 2.27/0.64    v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~sP6(sK2,sK4,sK3,sK1,sK0) | ~spl7_5),
% 2.27/0.64    inference(superposition,[],[f273,f200])).
% 2.27/0.64  fof(f200,plain,(
% 2.27/0.64    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | ~spl7_5),
% 2.27/0.64    inference(forward_demodulation,[],[f198,f126])).
% 2.27/0.64  fof(f126,plain,(
% 2.27/0.64    sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) | ~spl7_5),
% 2.27/0.64    inference(avatar_component_clause,[],[f125])).
% 2.27/0.64  fof(f198,plain,(
% 2.27/0.64    k7_relat_1(sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0)),
% 2.27/0.64    inference(resolution,[],[f192,f170])).
% 2.27/0.64  fof(f170,plain,(
% 2.27/0.64    m1_pre_topc(sK0,sK0)),
% 2.27/0.64    inference(global_subsumption,[],[f48,f52,f60,f62,f49,f53,f168])).
% 2.27/0.64  fof(f168,plain,(
% 2.27/0.64    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 2.27/0.64    inference(superposition,[],[f85,f50])).
% 2.27/0.64  fof(f50,plain,(
% 2.27/0.64    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f85,plain,(
% 2.27/0.64    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f29])).
% 2.27/0.64  fof(f29,plain,(
% 2.27/0.64    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/0.64    inference(flattening,[],[f28])).
% 2.27/0.64  fof(f28,plain,(
% 2.27/0.64    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/0.64    inference(ennf_transformation,[],[f14])).
% 2.27/0.64  fof(f14,plain,(
% 2.27/0.64    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.27/0.64    inference(pure_predicate_removal,[],[f9])).
% 2.27/0.64  fof(f9,axiom,(
% 2.27/0.64    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.27/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 2.27/0.64  fof(f52,plain,(
% 2.27/0.64    ~v2_struct_0(sK3)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f48,plain,(
% 2.27/0.64    ~v2_struct_0(sK4)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f273,plain,(
% 2.27/0.64    ( ! [X0,X1] : (v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~sP6(X1,sK4,sK3,X0,sK0)) )),
% 2.27/0.64    inference(global_subsumption,[],[f48,f52,f60,f61,f62,f49,f53,f51,f272])).
% 2.27/0.64  fof(f272,plain,(
% 2.27/0.64    ( ! [X0,X1] : (v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~sP6(X1,sK4,sK3,X0,sK0) | v2_struct_0(sK0)) )),
% 2.27/0.64    inference(superposition,[],[f78,f50])).
% 2.27/0.64  fof(f78,plain,(
% 2.27/0.64    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~sP6(X4,X3,X2,X1,X0) | v2_struct_0(X0)) )),
% 2.27/0.64    inference(cnf_transformation,[],[f22])).
% 2.27/0.64  fof(f51,plain,(
% 2.27/0.64    r4_tsep_1(sK0,sK3,sK4)),
% 2.27/0.64    inference(cnf_transformation,[],[f17])).
% 2.27/0.64  fof(f914,plain,(
% 2.27/0.64    ~spl7_37),
% 2.27/0.64    inference(avatar_contradiction_clause,[],[f913])).
% 2.27/0.64  fof(f913,plain,(
% 2.27/0.64    $false | ~spl7_37),
% 2.27/0.64    inference(resolution,[],[f516,f57])).
% 2.27/0.64  fof(f516,plain,(
% 2.27/0.64    v2_struct_0(sK1) | ~spl7_37),
% 2.27/0.64    inference(avatar_component_clause,[],[f515])).
% 2.27/0.64  fof(f871,plain,(
% 2.27/0.64    ~spl7_23 | ~spl7_29 | ~spl7_28 | spl7_45),
% 2.27/0.64    inference(avatar_split_clause,[],[f870,f845,f295,f342,f280])).
% 2.27/0.64  fof(f342,plain,(
% 2.27/0.64    spl7_29 <=> l1_struct_0(sK4)),
% 2.27/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 2.27/0.65  fof(f870,plain,(
% 2.27/0.65    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.27/0.65    inference(global_subsumption,[],[f54,f55,f56,f815])).
% 2.27/0.65  fof(f815,plain,(
% 2.27/0.65    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.27/0.65    inference(superposition,[],[f88,f196])).
% 2.27/0.65  fof(f869,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_29 | ~spl7_28 | spl7_43),
% 2.27/0.65    inference(avatar_split_clause,[],[f868,f837,f295,f342,f280])).
% 2.27/0.65  fof(f868,plain,(
% 2.27/0.65    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.27/0.65    inference(global_subsumption,[],[f54,f55,f56,f814])).
% 2.27/0.65  fof(f814,plain,(
% 2.27/0.65    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.27/0.65    inference(superposition,[],[f87,f196])).
% 2.27/0.65  fof(f867,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_29 | ~spl7_28 | spl7_42),
% 2.27/0.65    inference(avatar_split_clause,[],[f866,f833,f295,f342,f280])).
% 2.27/0.65  fof(f866,plain,(
% 2.27/0.65    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.27/0.65    inference(global_subsumption,[],[f54,f55,f56,f813])).
% 2.27/0.65  fof(f813,plain,(
% 2.27/0.65    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.27/0.65    inference(superposition,[],[f86,f196])).
% 2.27/0.65  fof(f850,plain,(
% 2.27/0.65    spl7_8 | spl7_44),
% 2.27/0.65    inference(avatar_split_clause,[],[f803,f841,f148])).
% 2.27/0.65  fof(f803,plain,(
% 2.27/0.65    ( ! [X6] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~sP5(sK4,X6,sK2,sK1,sK0)) )),
% 2.27/0.65    inference(superposition,[],[f41,f196])).
% 2.27/0.65  fof(f41,plain,(
% 2.27/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~sP5(X4,X3,X2,X1,X0)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f17])).
% 2.27/0.65  fof(f795,plain,(
% 2.27/0.65    spl7_17 | ~spl7_34),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f788])).
% 2.27/0.65  fof(f788,plain,(
% 2.27/0.65    $false | (spl7_17 | ~spl7_34)),
% 2.27/0.65    inference(resolution,[],[f507,f329])).
% 2.27/0.65  fof(f329,plain,(
% 2.27/0.65    ( ! [X0] : (~sP6(sK2,sK4,X0,sK1,sK0)) ) | spl7_17),
% 2.27/0.65    inference(resolution,[],[f255,f73])).
% 2.27/0.65  fof(f73,plain,(
% 2.27/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~sP6(X4,X3,X2,X1,X0)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f22])).
% 2.27/0.65  fof(f255,plain,(
% 2.27/0.65    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | spl7_17),
% 2.27/0.65    inference(avatar_component_clause,[],[f254])).
% 2.27/0.65  fof(f254,plain,(
% 2.27/0.65    spl7_17 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.27/0.65  fof(f507,plain,(
% 2.27/0.65    sP6(sK2,sK4,sK3,sK1,sK0) | ~spl7_34),
% 2.27/0.65    inference(avatar_component_clause,[],[f506])).
% 2.27/0.65  fof(f794,plain,(
% 2.27/0.65    spl7_21 | ~spl7_34),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f789])).
% 2.27/0.65  fof(f789,plain,(
% 2.27/0.65    $false | (spl7_21 | ~spl7_34)),
% 2.27/0.65    inference(resolution,[],[f507,f336])).
% 2.27/0.65  fof(f336,plain,(
% 2.27/0.65    ( ! [X1] : (~sP6(sK2,X1,sK3,sK1,sK0)) ) | spl7_21),
% 2.27/0.65    inference(resolution,[],[f267,f69])).
% 2.27/0.65  fof(f69,plain,(
% 2.27/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~sP6(X4,X3,X2,X1,X0)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f22])).
% 2.27/0.65  fof(f267,plain,(
% 2.27/0.65    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | spl7_21),
% 2.27/0.65    inference(avatar_component_clause,[],[f266])).
% 2.27/0.65  fof(f266,plain,(
% 2.27/0.65    spl7_21 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.27/0.65  fof(f778,plain,(
% 2.27/0.65    spl7_25),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f777])).
% 2.27/0.65  fof(f777,plain,(
% 2.27/0.65    $false | spl7_25),
% 2.27/0.65    inference(resolution,[],[f287,f56])).
% 2.27/0.65  fof(f287,plain,(
% 2.27/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl7_25),
% 2.27/0.65    inference(avatar_component_clause,[],[f286])).
% 2.27/0.65  fof(f523,plain,(
% 2.27/0.65    spl7_36),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f522])).
% 2.27/0.65  fof(f522,plain,(
% 2.27/0.65    $false | spl7_36),
% 2.27/0.65    inference(resolution,[],[f513,f58])).
% 2.27/0.65  fof(f513,plain,(
% 2.27/0.65    ~v2_pre_topc(sK1) | spl7_36),
% 2.27/0.65    inference(avatar_component_clause,[],[f512])).
% 2.27/0.65  fof(f519,plain,(
% 2.27/0.65    spl7_35),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f518])).
% 2.27/0.65  fof(f518,plain,(
% 2.27/0.65    $false | spl7_35),
% 2.27/0.65    inference(resolution,[],[f510,f59])).
% 2.27/0.65  fof(f510,plain,(
% 2.27/0.65    ~l1_pre_topc(sK1) | spl7_35),
% 2.27/0.65    inference(avatar_component_clause,[],[f509])).
% 2.27/0.65  fof(f517,plain,(
% 2.27/0.65    ~spl7_1 | spl7_34 | ~spl7_26 | ~spl7_27 | ~spl7_35 | ~spl7_36 | spl7_37 | ~spl7_25 | ~spl7_5),
% 2.27/0.65    inference(avatar_split_clause,[],[f498,f125,f286,f515,f512,f509,f292,f289,f506,f92])).
% 2.27/0.65  fof(f498,plain,(
% 2.27/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | sP6(sK2,sK4,sK3,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~spl7_5),
% 2.27/0.65    inference(duplicate_literal_removal,[],[f497])).
% 2.27/0.65  fof(f497,plain,(
% 2.27/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sP6(sK2,sK4,sK3,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~spl7_5),
% 2.27/0.65    inference(superposition,[],[f320,f200])).
% 2.27/0.65  fof(f320,plain,(
% 2.27/0.65    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | sP6(X1,sK4,sK3,X0,sK0) | ~v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0)) | ~v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)) )),
% 2.27/0.65    inference(global_subsumption,[],[f48,f52,f60,f61,f62,f49,f53,f51,f317])).
% 2.27/0.65  fof(f317,plain,(
% 2.27/0.65    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | sP6(X1,sK4,sK3,X0,sK0) | ~v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0)) | ~v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | v2_struct_0(sK0)) )),
% 2.27/0.65    inference(superposition,[],[f75,f50])).
% 2.27/0.65  fof(f75,plain,(
% 2.27/0.65    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP6(X4,X3,X2,X1,X0) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f22])).
% 2.27/0.65  fof(f391,plain,(
% 2.27/0.65    spl7_26),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f390])).
% 2.27/0.65  fof(f390,plain,(
% 2.27/0.65    $false | spl7_26),
% 2.27/0.65    inference(resolution,[],[f290,f55])).
% 2.27/0.65  fof(f290,plain,(
% 2.27/0.65    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl7_26),
% 2.27/0.65    inference(avatar_component_clause,[],[f289])).
% 2.27/0.65  fof(f372,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_24 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_20),
% 2.27/0.65    inference(avatar_split_clause,[],[f367,f263,f295,f292,f289,f286,f283,f280])).
% 2.27/0.65  fof(f263,plain,(
% 2.27/0.65    spl7_20 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 2.27/0.65  fof(f367,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_20),
% 2.27/0.65    inference(resolution,[],[f264,f88])).
% 2.27/0.65  fof(f264,plain,(
% 2.27/0.65    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_20),
% 2.27/0.65    inference(avatar_component_clause,[],[f263])).
% 2.27/0.65  fof(f365,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_29 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_16),
% 2.27/0.65    inference(avatar_split_clause,[],[f360,f251,f295,f292,f289,f286,f342,f280])).
% 2.27/0.65  fof(f251,plain,(
% 2.27/0.65    spl7_16 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.27/0.65  fof(f360,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0) | spl7_16),
% 2.27/0.65    inference(resolution,[],[f252,f88])).
% 2.27/0.65  fof(f252,plain,(
% 2.27/0.65    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl7_16),
% 2.27/0.65    inference(avatar_component_clause,[],[f251])).
% 2.27/0.65  fof(f359,plain,(
% 2.27/0.65    spl7_29),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f358])).
% 2.27/0.65  fof(f358,plain,(
% 2.27/0.65    $false | spl7_29),
% 2.27/0.65    inference(resolution,[],[f351,f106])).
% 2.27/0.65  fof(f106,plain,(
% 2.27/0.65    l1_pre_topc(sK4)),
% 2.27/0.65    inference(global_subsumption,[],[f62,f104])).
% 2.27/0.65  fof(f104,plain,(
% 2.27/0.65    ~l1_pre_topc(sK0) | l1_pre_topc(sK4)),
% 2.27/0.65    inference(resolution,[],[f65,f49])).
% 2.27/0.65  fof(f65,plain,(
% 2.27/0.65    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f20])).
% 2.27/0.65  fof(f20,plain,(
% 2.27/0.65    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/0.65    inference(ennf_transformation,[],[f7])).
% 2.27/0.65  fof(f7,axiom,(
% 2.27/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.27/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.27/0.65  fof(f351,plain,(
% 2.27/0.65    ~l1_pre_topc(sK4) | spl7_29),
% 2.27/0.65    inference(resolution,[],[f343,f64])).
% 2.27/0.65  fof(f64,plain,(
% 2.27/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f19])).
% 2.27/0.65  fof(f19,plain,(
% 2.27/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.27/0.65    inference(ennf_transformation,[],[f6])).
% 2.27/0.65  fof(f6,axiom,(
% 2.27/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.27/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.27/0.65  fof(f343,plain,(
% 2.27/0.65    ~l1_struct_0(sK4) | spl7_29),
% 2.27/0.65    inference(avatar_component_clause,[],[f342])).
% 2.27/0.65  fof(f357,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_24 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_22),
% 2.27/0.65    inference(avatar_split_clause,[],[f352,f269,f295,f292,f289,f286,f283,f280])).
% 2.27/0.65  fof(f269,plain,(
% 2.27/0.65    spl7_22 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.27/0.65  fof(f352,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_22),
% 2.27/0.65    inference(resolution,[],[f270,f87])).
% 2.27/0.65  fof(f270,plain,(
% 2.27/0.65    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_22),
% 2.27/0.65    inference(avatar_component_clause,[],[f269])).
% 2.27/0.65  fof(f350,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_29 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_18),
% 2.27/0.65    inference(avatar_split_clause,[],[f345,f257,f295,f292,f289,f286,f342,f280])).
% 2.27/0.65  fof(f257,plain,(
% 2.27/0.65    spl7_18 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.27/0.65  fof(f345,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0) | spl7_18),
% 2.27/0.65    inference(resolution,[],[f258,f87])).
% 2.27/0.65  fof(f258,plain,(
% 2.27/0.65    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | spl7_18),
% 2.27/0.65    inference(avatar_component_clause,[],[f257])).
% 2.27/0.65  fof(f344,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_29 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_19),
% 2.27/0.65    inference(avatar_split_clause,[],[f322,f260,f295,f292,f289,f286,f342,f280])).
% 2.27/0.65  fof(f260,plain,(
% 2.27/0.65    spl7_19 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.27/0.65  fof(f322,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0) | spl7_19),
% 2.27/0.65    inference(resolution,[],[f261,f86])).
% 2.27/0.65  fof(f261,plain,(
% 2.27/0.65    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | spl7_19),
% 2.27/0.65    inference(avatar_component_clause,[],[f260])).
% 2.27/0.65  fof(f340,plain,(
% 2.27/0.65    spl7_28),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f339])).
% 2.27/0.65  fof(f339,plain,(
% 2.27/0.65    $false | spl7_28),
% 2.27/0.65    inference(resolution,[],[f321,f59])).
% 2.27/0.65  fof(f321,plain,(
% 2.27/0.65    ~l1_pre_topc(sK1) | spl7_28),
% 2.27/0.65    inference(resolution,[],[f296,f64])).
% 2.27/0.65  fof(f296,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | spl7_28),
% 2.27/0.65    inference(avatar_component_clause,[],[f295])).
% 2.27/0.65  fof(f334,plain,(
% 2.27/0.65    spl7_24),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f333])).
% 2.27/0.65  fof(f333,plain,(
% 2.27/0.65    $false | spl7_24),
% 2.27/0.65    inference(resolution,[],[f308,f107])).
% 2.27/0.65  fof(f107,plain,(
% 2.27/0.65    l1_pre_topc(sK3)),
% 2.27/0.65    inference(global_subsumption,[],[f62,f105])).
% 2.27/0.65  fof(f105,plain,(
% 2.27/0.65    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 2.27/0.65    inference(resolution,[],[f65,f53])).
% 2.27/0.65  fof(f308,plain,(
% 2.27/0.65    ~l1_pre_topc(sK3) | spl7_24),
% 2.27/0.65    inference(resolution,[],[f284,f64])).
% 2.27/0.65  fof(f284,plain,(
% 2.27/0.65    ~l1_struct_0(sK3) | spl7_24),
% 2.27/0.65    inference(avatar_component_clause,[],[f283])).
% 2.27/0.65  fof(f328,plain,(
% 2.27/0.65    spl7_23),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f327])).
% 2.27/0.65  fof(f327,plain,(
% 2.27/0.65    $false | spl7_23),
% 2.27/0.65    inference(resolution,[],[f300,f62])).
% 2.27/0.65  fof(f300,plain,(
% 2.27/0.65    ~l1_pre_topc(sK0) | spl7_23),
% 2.27/0.65    inference(resolution,[],[f281,f64])).
% 2.27/0.65  fof(f281,plain,(
% 2.27/0.65    ~l1_struct_0(sK0) | spl7_23),
% 2.27/0.65    inference(avatar_component_clause,[],[f280])).
% 2.27/0.65  fof(f310,plain,(
% 2.27/0.65    spl7_27),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f309])).
% 2.27/0.65  fof(f309,plain,(
% 2.27/0.65    $false | spl7_27),
% 2.27/0.65    inference(resolution,[],[f293,f54])).
% 2.27/0.65  fof(f293,plain,(
% 2.27/0.65    ~v1_funct_1(sK2) | spl7_27),
% 2.27/0.65    inference(avatar_component_clause,[],[f292])).
% 2.27/0.65  fof(f297,plain,(
% 2.27/0.65    ~spl7_23 | ~spl7_24 | ~spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_15),
% 2.27/0.65    inference(avatar_split_clause,[],[f274,f248,f295,f292,f289,f286,f283,f280])).
% 2.27/0.65  fof(f248,plain,(
% 2.27/0.65    spl7_15 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.27/0.65  fof(f274,plain,(
% 2.27/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_15),
% 2.27/0.65    inference(resolution,[],[f249,f86])).
% 2.27/0.65  fof(f249,plain,(
% 2.27/0.65    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_15),
% 2.27/0.65    inference(avatar_component_clause,[],[f248])).
% 2.27/0.65  fof(f271,plain,(
% 2.27/0.65    ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_22 | spl7_2),
% 2.27/0.65    inference(avatar_split_clause,[],[f246,f95,f269,f266,f263,f260,f257,f254,f251,f248])).
% 2.27/0.65  fof(f246,plain,(
% 2.27/0.65    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.27/0.65    inference(resolution,[],[f102,f34])).
% 2.27/0.65  fof(f34,plain,(
% 2.27/0.65    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X3,X2,X1,X0) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 2.27/0.65    inference(cnf_transformation,[],[f17])).
% 2.27/0.65  fof(f102,plain,(
% 2.27/0.65    ~sP5(sK4,sK3,sK2,sK1,sK0) | spl7_2),
% 2.27/0.65    inference(avatar_component_clause,[],[f95])).
% 2.27/0.65  fof(f128,plain,(
% 2.27/0.65    spl7_5 | ~spl7_3),
% 2.27/0.65    inference(avatar_split_clause,[],[f123,f110,f125])).
% 2.27/0.65  fof(f110,plain,(
% 2.27/0.65    spl7_3 <=> v1_relat_1(sK2)),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.27/0.65  fof(f123,plain,(
% 2.27/0.65    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,u1_struct_0(sK0))),
% 2.27/0.65    inference(resolution,[],[f120,f82])).
% 2.27/0.65  fof(f82,plain,(
% 2.27/0.65    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 2.27/0.65    inference(cnf_transformation,[],[f26])).
% 2.27/0.65  fof(f26,plain,(
% 2.27/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.27/0.65    inference(flattening,[],[f25])).
% 2.27/0.65  fof(f25,plain,(
% 2.27/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.27/0.65    inference(ennf_transformation,[],[f3])).
% 2.27/0.65  fof(f3,axiom,(
% 2.27/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.27/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 2.27/0.65  fof(f120,plain,(
% 2.27/0.65    v4_relat_1(sK2,u1_struct_0(sK0))),
% 2.27/0.65    inference(resolution,[],[f83,f56])).
% 2.27/0.65  fof(f83,plain,(
% 2.27/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f27])).
% 2.27/0.65  fof(f27,plain,(
% 2.27/0.65    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.65    inference(ennf_transformation,[],[f15])).
% 2.27/0.65  fof(f15,plain,(
% 2.27/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.27/0.65    inference(pure_predicate_removal,[],[f4])).
% 2.27/0.65  fof(f4,axiom,(
% 2.27/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.27/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.27/0.65  fof(f117,plain,(
% 2.27/0.65    spl7_4),
% 2.27/0.65    inference(avatar_contradiction_clause,[],[f116])).
% 2.27/0.65  fof(f116,plain,(
% 2.27/0.65    $false | spl7_4),
% 2.27/0.65    inference(resolution,[],[f114,f81])).
% 2.27/0.65  fof(f81,plain,(
% 2.27/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.27/0.65    inference(cnf_transformation,[],[f2])).
% 2.27/0.65  fof(f2,axiom,(
% 2.27/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.27/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.27/0.65  fof(f114,plain,(
% 2.27/0.65    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl7_4),
% 2.27/0.65    inference(avatar_component_clause,[],[f113])).
% 2.27/0.65  fof(f113,plain,(
% 2.27/0.65    spl7_4 <=> v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 2.27/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.27/0.65  fof(f115,plain,(
% 2.27/0.65    spl7_3 | ~spl7_4),
% 2.27/0.65    inference(avatar_split_clause,[],[f108,f113,f110])).
% 2.27/0.65  fof(f108,plain,(
% 2.27/0.65    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | v1_relat_1(sK2)),
% 2.27/0.65    inference(resolution,[],[f63,f56])).
% 2.27/0.65  fof(f63,plain,(
% 2.27/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.27/0.65    inference(cnf_transformation,[],[f18])).
% 2.27/0.65  fof(f18,plain,(
% 2.27/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.27/0.65    inference(ennf_transformation,[],[f1])).
% 2.27/0.65  fof(f1,axiom,(
% 2.27/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.27/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.27/0.65  fof(f103,plain,(
% 2.27/0.65    ~spl7_1 | ~spl7_2),
% 2.27/0.65    inference(avatar_split_clause,[],[f100,f95,f92])).
% 2.27/0.65  fof(f100,plain,(
% 2.27/0.65    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.27/0.65    inference(global_subsumption,[],[f90,f98,f99,f43])).
% 2.27/0.65  fof(f43,plain,(
% 2.27/0.65    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.27/0.65    inference(cnf_transformation,[],[f17])).
% 2.27/0.65  fof(f99,plain,(
% 2.27/0.65    v1_funct_1(sK2)),
% 2.27/0.65    inference(global_subsumption,[],[f54])).
% 2.27/0.65  fof(f98,plain,(
% 2.27/0.65    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.27/0.65    inference(global_subsumption,[],[f55])).
% 2.27/0.65  fof(f90,plain,(
% 2.27/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.27/0.65    inference(global_subsumption,[],[f56])).
% 2.27/0.65  fof(f97,plain,(
% 2.27/0.65    spl7_1 | spl7_2),
% 2.27/0.65    inference(avatar_split_clause,[],[f46,f95,f92])).
% 2.27/0.65  fof(f46,plain,(
% 2.27/0.65    sP5(sK4,sK3,sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 2.27/0.65    inference(cnf_transformation,[],[f17])).
% 2.27/0.65  % SZS output end Proof for theBenchmark
% 2.27/0.65  % (19803)------------------------------
% 2.27/0.65  % (19803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.65  % (19803)Termination reason: Refutation
% 2.27/0.65  
% 2.27/0.65  % (19803)Memory used [KB]: 12792
% 2.27/0.65  % (19803)Time elapsed: 0.233 s
% 2.27/0.65  % (19803)------------------------------
% 2.27/0.65  % (19803)------------------------------
% 2.27/0.65  % (19790)Success in time 0.298 s
%------------------------------------------------------------------------------

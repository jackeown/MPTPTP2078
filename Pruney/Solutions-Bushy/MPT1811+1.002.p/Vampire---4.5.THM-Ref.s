%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1811+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  169 (2985 expanded)
%              Number of leaves         :   16 (1202 expanded)
%              Depth                    :   40
%              Number of atoms          : 1460 (107493 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f123,f186,f224,f230,f254,f278])).

fof(f278,plain,
    ( spl7_1
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f263,f107])).

fof(f107,plain,
    ( ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_1
  <=> v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f263,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f219,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        | ~ v1_funct_1(X4) )
      & ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(X4) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( ( sP0(X1,X3,X2,X0,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        | ~ v1_funct_1(X4) )
      & ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
        | ~ sP0(X1,X3,X2,X0,X4) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( ( sP0(X1,X3,X2,X0,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        | ~ v1_funct_1(X4) )
      & ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
        | ~ sP0(X1,X3,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f219,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_5
  <=> sP0(sK3,sK5,sK4,sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f254,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f252,f107])).

fof(f252,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f74,f251])).

fof(f251,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f250,f112])).

fof(f112,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_2
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f250,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f249,f241])).

fof(f241,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f50,f107])).

fof(f50,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6) )
    & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
        & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
        & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
        & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) )
      | ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
        & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        & v1_funct_1(sK6) ) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_borsuk_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_borsuk_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
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
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_borsuk_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_borsuk_1(X2,sK2)
              & ~ v2_struct_0(X2) )
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
                    ( ( ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                    & ( ( m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                        & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                        & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                      | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                        & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & v1_borsuk_1(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & v1_borsuk_1(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                    | ~ v1_funct_1(X4) )
                  & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                      & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                      & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                      & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                      & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                      & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                    | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                      & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                      & v1_funct_1(X4) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & v1_borsuk_1(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & v1_borsuk_1(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                  | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                  | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                  | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                  | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                  | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                  | ~ v1_funct_1(X4) )
                & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3)
                    & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4))
                    & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3)
                    & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                  | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                    & v1_funct_1(X4) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & v1_borsuk_1(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & v1_borsuk_1(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
                | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
                | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
                | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
                | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                | ~ v1_funct_1(X4) )
              & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
                  & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
                  & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                  & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
                  & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
                  & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4)) )
                | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                  & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                  & v1_funct_1(X4) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & v1_borsuk_1(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & v1_borsuk_1(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
              | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
              | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
              | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
              | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
              | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
              | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
              | ~ v1_funct_1(X4) )
            & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3)
                & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4))
                & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3)
                & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
                & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4)) )
              | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3)
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                & v1_funct_1(X4) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & v1_borsuk_1(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
            | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
            | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
            | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
            | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
            | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
            | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
            | ~ v1_funct_1(X4) )
          & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
              & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
              & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
              & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
              & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4)) )
            | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
              & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
              & v1_funct_1(X4) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & v1_borsuk_1(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

% (13879)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f20,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
          | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
          | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
          | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
          | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
          | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          | ~ v1_funct_1(X4) )
        & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3)
            & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4))
            & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3)
            & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3))
            & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4)) )
          | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
            & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
            & v1_funct_1(X4) ) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
        | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6) )
      & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
          & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
          & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
          & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
          & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) )
        | ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
          & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          & v1_funct_1(sK6) ) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_tmap_1)).

fof(f249,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f248,f239])).

fof(f239,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f54,f107])).

fof(f54,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f248,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f247,f223])).

fof(f223,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_6
  <=> sP1(sK3,sK5,sK6,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f247,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f246,f122])).

fof(f122,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_3
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f246,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f245,f242])).

fof(f242,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f66,f107])).

fof(f66,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f245,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f244,f240])).

fof(f240,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f70,f107])).

fof(f70,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f244,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | spl7_1 ),
    inference(resolution,[],[f243,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | sP1(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP1(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP1(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP1(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP1(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP1(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f243,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f58,f107])).

fof(f58,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f230,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f228,f40])).

fof(f40,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f228,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f227,f36])).

fof(f36,plain,(
    v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f227,plain,
    ( ~ v1_borsuk_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f226,f37])).

fof(f37,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f226,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f225,f39])).

fof(f39,plain,(
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f225,plain,
    ( ~ v1_borsuk_1(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | spl7_4 ),
    inference(resolution,[],[f215,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r4_tsep_1(sK2,X1,X0)
      | ~ v1_borsuk_1(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f95,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ v1_borsuk_1(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | r4_tsep_1(sK2,X1,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f30,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ v1_borsuk_1(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | r4_tsep_1(sK2,X1,X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f31,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
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
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
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
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f215,plain,
    ( ~ r4_tsep_1(sK2,sK4,sK5)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_4
  <=> r4_tsep_1(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f224,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f200,f221,f217,f213])).

fof(f200,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5) ),
    inference(subsumption_resolution,[],[f199,f29])).

fof(f199,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f198,f30])).

fof(f198,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f197,f31])).

fof(f197,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f196,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f196,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f195,f33])).

fof(f33,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f195,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f194,f34])).

fof(f34,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f194,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f193,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f193,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f192,f37])).

fof(f192,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f191,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f191,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f190,f40])).

fof(f190,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f165,f42])).

fof(f42,plain,(
    v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f165,plain,
    ( ~ sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ r4_tsep_1(sK2,sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f101,f43])).

fof(f43,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X6,X5)),u1_struct_0(X4))))
      | ~ sP1(X4,X5,sK6,X6,X7)
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X7,X6,X5)),u1_struct_0(X4))
      | sP0(X4,X5,X6,X7,sK6)
      | ~ r4_tsep_1(X7,X6,X5)
      | ~ m1_pre_topc(X5,X7)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f41,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ sP1(X1,X3,X4,X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | sP0(X1,X3,X2,X0,X4)
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
                          | ~ sP1(X1,X3,X4,X2,X0) )
                        & ( sP1(X1,X3,X4,X2,X0)
                          | ~ sP0(X1,X3,X2,X0,X4) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                      <=> sP1(X1,X3,X4,X2,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f41,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f186,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f151,f184])).

fof(f184,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f183,f41])).

fof(f183,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f182,f42])).

fof(f182,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f181,f108])).

fof(f108,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f181,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f180,f43])).

fof(f180,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f179,f152])).

fof(f152,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f150,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f149,f36])).

fof(f149,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f148,f39])).

fof(f148,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f147,f32])).

fof(f147,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f146,f33])).

fof(f146,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f145,f34])).

fof(f145,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f144,f35])).

fof(f144,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f143,f37])).

fof(f143,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f142,f38])).

fof(f142,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,
    ( sP1(sK3,sK5,sK6,sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f140,f131])).

fof(f131,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f130,f42])).

fof(f130,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | sP0(sK3,sK5,sK4,sK2,sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f129,f108])).

fof(f129,plain,
    ( ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | sP0(sK3,sK5,sK4,sK2,sK6) ),
    inference(resolution,[],[f102,f43])).

fof(f102,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X8,X9,X10)),u1_struct_0(X11))))
      | ~ v5_pre_topc(sK6,k1_tsep_1(X8,X9,X10),X11)
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X8,X9,X10)),u1_struct_0(X11))
      | sP0(X11,X10,X9,X8,sK6) ) ),
    inference(resolution,[],[f41,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2,sK2,sK6)
      | sP1(X0,X1,sK6,X2,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_borsuk_1(X1,sK2)
      | ~ v1_borsuk_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f139,f29])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,sK6,X2,sK2)
      | ~ sP0(X0,X1,X2,sK2,sK6)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | ~ v1_borsuk_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f138,f30])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,sK6,X2,sK2)
      | ~ sP0(X0,X1,X2,sK2,sK6)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | ~ v1_borsuk_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f137,f31])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,sK6,X2,sK2)
      | ~ sP0(X0,X1,X2,sK2,sK6)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | ~ v1_borsuk_1(X2,sK2) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,sK6,X2,sK2)
      | ~ sP0(X0,X1,X2,sK2,sK6)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_borsuk_1(X1,sK2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ v1_borsuk_1(X2,sK2)
      | ~ m1_pre_topc(X1,sK2) ) ),
    inference(resolution,[],[f104,f96])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_tsep_1(X3,X2,X1)
      | sP1(X0,X1,sK6,X2,X3)
      | ~ sP0(X0,X1,X2,X3,sK6)
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f103,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,sK6)
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | sP1(X0,X1,sK6,X2,X3)
      | ~ r4_tsep_1(X3,X2,X1)
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f100,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,sK6)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | sP1(X0,X1,sK6,X2,X3)
      | ~ r4_tsep_1(X3,X2,X1)
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f41,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ sP0(X1,X3,X2,X0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | sP1(X1,X3,X4,X2,X0)
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

fof(f179,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f178,f153])).

fof(f153,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f178,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f177,f154])).

fof(f154,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f177,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f176,f155])).

fof(f155,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f176,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f175,f156])).

fof(f156,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f175,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f174,f157])).

fof(f157,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f174,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f76,f158])).

fof(f158,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ spl7_1 ),
    inference(resolution,[],[f150,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f62,f120,f106])).

fof(f62,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f113,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f46,f110,f106])).

fof(f46,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 (1050 expanded)
%              Number of leaves         :   22 ( 418 expanded)
%              Depth                    :   23
%              Number of atoms          : 1385 (34564 expanded)
%              Number of equality atoms :   24 ( 978 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f140,f149,f186,f190,f199,f281,f291,f300,f304,f318,f330])).

fof(f330,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f295,f118])).

fof(f118,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_2
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f295,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f289,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
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
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
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
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
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
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP0(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f289,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f288,f135])).

fof(f135,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_4
  <=> sP1(sK5,sK2,sK4,sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f288,plain,
    ( ! [X2,X3] :
        ( ~ sP1(X3,sK2,sK4,X2,sK3)
        | sP0(sK3,X2,sK4,sK2,X3) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f111,f115])).

fof(f115,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_1
  <=> v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f111,plain,(
    ! [X2,X3] :
      ( sP0(sK3,X2,sK4,sK2,X3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ sP1(X3,sK2,sK4,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
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
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK2,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK4) ) )
    & sK2 = k1_tsep_1(sK2,sK5,sK6)
    & m1_pre_topc(sK6,sK2)
    & v1_borsuk_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_borsuk_1(sK5,sK2)
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
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) ) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK2,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK2,X1)
                          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & sK2 = k1_tsep_1(sK2,X3,X4)
                      & m1_pre_topc(X4,sK2)
                      & v1_borsuk_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_borsuk_1(X3,sK2)
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
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X2,sK2,X1)
                      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        & v5_pre_topc(X2,sK2,X1)
                        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        & v1_funct_1(X2) ) )
                    & sK2 = k1_tsep_1(sK2,X3,X4)
                    & m1_pre_topc(X4,sK2)
                    & v1_borsuk_1(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & v1_borsuk_1(X3,sK2)
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
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(X2,sK2,sK3)
                    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                      & v5_pre_topc(X2,sK2,sK3)
                      & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                      & v1_funct_1(X2) ) )
                  & sK2 = k1_tsep_1(sK2,X3,X4)
                  & m1_pre_topc(X4,sK2)
                  & v1_borsuk_1(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & v1_borsuk_1(X3,sK2)
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
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(X2,sK2,sK3)
                  | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                  | ~ v1_funct_1(X2) )
                & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    & v5_pre_topc(X2,sK2,sK3)
                    & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    & v1_funct_1(X2) ) )
                & sK2 = k1_tsep_1(sK2,X3,X4)
                & m1_pre_topc(X4,sK2)
                & v1_borsuk_1(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & v1_borsuk_1(X3,sK2)
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
                | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                | ~ v5_pre_topc(sK4,sK2,sK3)
                | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                | ~ v1_funct_1(sK4) )
              & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                  & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
                | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v5_pre_topc(sK4,sK2,sK3)
                  & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(sK4) ) )
              & sK2 = k1_tsep_1(sK2,X3,X4)
              & m1_pre_topc(X4,sK2)
              & v1_borsuk_1(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & v1_borsuk_1(X3,sK2)
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
              | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              | ~ v5_pre_topc(sK4,sK2,sK3)
              | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              | ~ v1_funct_1(sK4) )
            & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
              | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v5_pre_topc(sK4,sK2,sK3)
                & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(sK4) ) )
            & sK2 = k1_tsep_1(sK2,X3,X4)
            & m1_pre_topc(X4,sK2)
            & v1_borsuk_1(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & v1_borsuk_1(X3,sK2)
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
            | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            | ~ v5_pre_topc(sK4,sK2,sK3)
            | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            | ~ v1_funct_1(sK4) )
          & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
            | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v5_pre_topc(sK4,sK2,sK3)
              & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(sK4) ) )
          & sK2 = k1_tsep_1(sK2,sK5,X4)
          & m1_pre_topc(X4,sK2)
          & v1_borsuk_1(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & v1_borsuk_1(sK5,sK2)
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
          | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          | ~ v5_pre_topc(sK4,sK2,sK3)
          | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          | ~ v1_funct_1(sK4) )
        & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
          | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v5_pre_topc(sK4,sK2,sK3)
            & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(sK4) ) )
        & sK2 = k1_tsep_1(sK2,sK5,X4)
        & m1_pre_topc(X4,sK2)
        & v1_borsuk_1(X4,sK2)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK4,sK2,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4) )
      & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
          & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
        | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(sK4,sK2,sK3)
          & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(sK4) ) )
      & sK2 = k1_tsep_1(sK2,sK5,sK6)
      & m1_pre_topc(sK6,sK2)
      & v1_borsuk_1(sK6,sK2)
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
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_tmap_1)).

fof(f110,plain,(
    ! [X2,X3] :
      ( sP0(sK3,X2,sK4,sK2,X3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ sP1(X3,sK2,sK4,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f35,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X2,X3] :
      ( sP0(sK3,X2,sK4,sK2,X3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ sP1(X3,sK2,sK4,X2,sK3) ) ),
    inference(resolution,[],[f36,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(X2,X1,X4)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
            & v5_pre_topc(X2,X1,X4)
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,X1,X4)
          | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f318,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_11 ),
    inference(resolution,[],[f315,f289])).

fof(f315,plain,
    ( ! [X1] : ~ sP0(sK3,sK6,sK4,sK2,X1)
    | spl8_11 ),
    inference(resolution,[],[f185,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f185,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_11
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f304,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_10 ),
    inference(resolution,[],[f302,f289])).

fof(f302,plain,
    ( ! [X1] : ~ sP0(sK3,sK6,sK4,sK2,X1)
    | spl8_10 ),
    inference(resolution,[],[f181,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f181,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl8_10
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f300,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_9 ),
    inference(resolution,[],[f298,f289])).

fof(f298,plain,
    ( ! [X1] : ~ sP0(sK3,sK6,sK4,sK2,X1)
    | spl8_9 ),
    inference(resolution,[],[f177,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f177,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_9
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f291,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f289,f285])).

fof(f285,plain,
    ( ! [X0] : ~ sP0(sK3,X0,sK4,sK2,sK5)
    | spl8_8 ),
    inference(resolution,[],[f173,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f173,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_8
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f281,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f279,f203])).

fof(f203,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f158,f114])).

fof(f114,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f158,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f135,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | v5_pre_topc(X2,X1,X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f279,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f278,f124])).

fof(f124,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_3
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f278,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f277,f206])).

fof(f206,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f66,f114])).

fof(f66,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f277,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f266,f204])).

fof(f204,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f70,f114])).

fof(f70,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f266,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(resolution,[],[f213,f223])).

fof(f223,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f74,f114])).

fof(f74,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f212,f119])).

fof(f119,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f211,f205])).

fof(f205,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f50,f114])).

fof(f50,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f208,f168])).

fof(f168,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_7
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | spl8_1 ),
    inference(resolution,[],[f207,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f207,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f58,f114])).

fof(f58,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f199,plain,
    ( ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f197,f191])).

fof(f191,plain,
    ( ! [X0] : ~ sP0(sK3,X0,sK4,sK2,sK5)
    | spl8_7 ),
    inference(resolution,[],[f169,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f169,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f197,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl8_4
    | spl8_7 ),
    inference(resolution,[],[f196,f135])).

fof(f196,plain,
    ( ! [X2,X3] :
        ( ~ sP1(X3,sK2,sK4,X2,sK3)
        | sP0(sK3,X2,sK4,sK2,X3) )
    | spl8_7 ),
    inference(subsumption_resolution,[],[f111,f195])).

fof(f195,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | spl8_7 ),
    inference(subsumption_resolution,[],[f54,f169])).

fof(f54,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f190,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6 ),
    inference(resolution,[],[f187,f155])).

fof(f155,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f135,f126])).

fof(f126,plain,
    ( ! [X2,X3] :
        ( ~ sP1(X3,sK2,sK4,X2,sK3)
        | sP0(sK3,X2,sK4,sK2,X3) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f111,f115])).

fof(f187,plain,
    ( ! [X0] : ~ sP0(sK3,X0,sK4,sK2,sK5)
    | spl8_6 ),
    inference(resolution,[],[f165,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f165,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_6
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f186,plain,
    ( ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f161,f133,f117,f113,f183,f179,f175,f171,f167,f163])).

fof(f161,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f154,f160])).

fof(f160,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f155,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f154,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f153,f34])).

fof(f153,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f152,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f151,f115])).

fof(f151,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f150,f36])).

fof(f150,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f76,f119])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f149,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f147,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f147,plain,
    ( v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f146,f29])).

fof(f29,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f145,f30])).

fof(f30,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f144,f38])).

fof(f38,plain,(
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,
    ( ~ v1_borsuk_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f143,f39])).

fof(f39,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f142,f41])).

fof(f41,plain,(
    v1_borsuk_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f142,plain,
    ( ~ v1_borsuk_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f42,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | ~ v1_borsuk_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(resolution,[],[f139,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f139,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_5
  <=> r4_tsep_1(sK2,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f140,plain,
    ( spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f131,f137,f133])).

fof(f131,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f130,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f130,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f129,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f128,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f128,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f127,f42])).

fof(f127,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(resolution,[],[f109,f98])).

fof(f98,plain,(
    sQ7_eqProxy(k1_tsep_1(sK2,sK5,sK6),sK2) ),
    inference(resolution,[],[f94,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ sQ7_eqProxy(X0,X1)
      | sQ7_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f93])).

fof(f93,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f94,plain,(
    sQ7_eqProxy(sK2,k1_tsep_1(sK2,sK5,sK6)) ),
    inference(equality_proxy_replacement,[],[f43,f93])).

fof(f43,plain,(
    sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ r4_tsep_1(sK2,X0,X1)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f107,f29])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f106,f30])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f105,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f104,f32])).

fof(f32,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f33,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f102,f34])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r4_tsep_1(sK2,X0,X1)
      | ~ sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | sP1(X0,sK2,sK4,X1,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f36,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ r4_tsep_1(X0,X3,X4)
      | ~ sQ7_eqProxy(k1_tsep_1(X0,X3,X4),X0)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | sP1(X3,X0,X2,X4,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f91,f93])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X3,X0,X2,X4,X1)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X3,X0,X2,X4,X1)
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
    inference(definition_folding,[],[f8,f12,f11])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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

fof(f125,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f62,f122,f113])).

fof(f62,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f120,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f46,f117,f113])).

fof(f46,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:40:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (8956)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (8957)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (8955)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (8954)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (8966)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (8972)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (8959)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (8976)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (8971)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (8968)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (8956)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (8953)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (8964)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (8960)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (8975)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (8974)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (8967)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (8962)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (8958)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (8969)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (8960)Refutation not found, incomplete strategy% (8960)------------------------------
% 0.21/0.52  % (8960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8960)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8960)Memory used [KB]: 6268
% 0.21/0.52  % (8960)Time elapsed: 0.070 s
% 0.21/0.52  % (8960)------------------------------
% 0.21/0.52  % (8960)------------------------------
% 0.21/0.52  % (8963)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (8970)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (8965)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (8973)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f120,f125,f140,f149,f186,f190,f199,f281,f291,f300,f304,f318,f330])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    ~spl8_1 | spl8_2 | ~spl8_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    $false | (~spl8_1 | spl8_2 | ~spl8_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f295,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl8_2 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | (~spl8_1 | ~spl8_4)),
% 0.21/0.53    inference(resolution,[],[f289,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 0.21/0.53    inference(rectify,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X4,X2,X0,X3] : ((sP0(X1,X4,X2,X0,X3) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP0(X1,X4,X2,X0,X3)))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X4,X2,X0,X3] : ((sP0(X1,X4,X2,X0,X3) | (~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP0(X1,X4,X2,X0,X3)))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X1,X4,X2,X0,X3] : (sP0(X1,X4,X2,X0,X3) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    sP0(sK3,sK6,sK4,sK2,sK5) | (~spl8_1 | ~spl8_4)),
% 0.21/0.53    inference(resolution,[],[f288,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    sP1(sK5,sK2,sK4,sK6,sK3) | ~spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl8_4 <=> sP1(sK5,sK2,sK4,sK6,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~sP1(X3,sK2,sK4,X2,sK3) | sP0(sK3,X2,sK4,sK2,X3)) ) | ~spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f111,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    v5_pre_topc(sK4,sK2,sK3) | ~spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl8_1 <=> v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X2,X3] : (sP0(sK3,X2,sK4,sK2,X3) | ~v5_pre_topc(sK4,sK2,sK3) | ~sP1(X3,sK2,sK4,X2,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f110,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & v1_borsuk_1(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & v1_borsuk_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f20,f19,f18,f17,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,sK2) & v1_borsuk_1(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & v1_borsuk_1(sK6,sK2) & ~v2_struct_0(sK6))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f5])).
% 0.21/0.53  fof(f5,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f3])).
% 0.21/0.53  fof(f3,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_tmap_1)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X2,X3] : (sP0(sK3,X2,sK4,sK2,X3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~sP1(X3,sK2,sK4,X2,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f101,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X2,X3] : (sP0(sK3,X2,sK4,sK2,X3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~sP1(X3,sK2,sK4,X2,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f36,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) | sP0(X4,X3,X2,X1,X0) | ~v5_pre_topc(X2,X1,X4) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) & v5_pre_topc(X2,X1,X4) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) | ~v5_pre_topc(X2,X1,X4) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 0.21/0.53    inference(rectify,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X3,X0,X2,X4,X1] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X4,X2,X0,X3)) & (sP0(X1,X4,X2,X0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~sP1(X3,X0,X2,X4,X1))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X3,X0,X2,X4,X1] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) | ~sP0(X1,X4,X2,X0,X3)) & (sP0(X1,X4,X2,X0,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)))) | ~sP1(X3,X0,X2,X4,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X3,X0,X2,X4,X1] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> sP0(X1,X4,X2,X0,X3)) | ~sP1(X3,X0,X2,X4,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_4 | spl8_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    $false | (~spl8_1 | ~spl8_4 | spl8_11)),
% 0.21/0.53    inference(resolution,[],[f315,f289])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ( ! [X1] : (~sP0(sK3,sK6,sK4,sK2,X1)) ) | spl8_11),
% 0.21/0.53    inference(resolution,[],[f185,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl8_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl8_11 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.53  fof(f304,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_4 | spl8_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    $false | (~spl8_1 | ~spl8_4 | spl8_10)),
% 0.21/0.53    inference(resolution,[],[f302,f289])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    ( ! [X1] : (~sP0(sK3,sK6,sK4,sK2,X1)) ) | spl8_10),
% 0.21/0.53    inference(resolution,[],[f181,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    spl8_10 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_4 | spl8_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    $false | (~spl8_1 | ~spl8_4 | spl8_9)),
% 0.21/0.53    inference(resolution,[],[f298,f289])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    ( ! [X1] : (~sP0(sK3,sK6,sK4,sK2,X1)) ) | spl8_9),
% 0.21/0.53    inference(resolution,[],[f177,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f175])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    spl8_9 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.53  fof(f291,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_4 | spl8_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    $false | (~spl8_1 | ~spl8_4 | spl8_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f285])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK3,X0,sK4,sK2,sK5)) ) | spl8_8),
% 0.21/0.53    inference(resolution,[],[f173,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl8_8 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    $false | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f279,f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ~sP0(sK3,sK6,sK4,sK2,sK5) | (spl8_1 | ~spl8_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~v5_pre_topc(sK4,sK2,sK3) | spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ~sP0(sK3,sK6,sK4,sK2,sK5) | v5_pre_topc(sK4,sK2,sK3) | ~spl8_4),
% 0.21/0.53    inference(resolution,[],[f135,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X4,X3,X2,X1,X0) | v5_pre_topc(X2,X1,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    sP0(sK3,sK6,sK4,sK2,sK5) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f278,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    spl8_3 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | sP0(sK3,sK6,sK4,sK2,sK5) | (spl8_1 | ~spl8_2 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f277,f206])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f66,f114])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | sP0(sK3,sK6,sK4,sK2,sK5) | (spl8_1 | ~spl8_2 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f266,f204])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f70,f114])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | sP0(sK3,sK6,sK4,sK2,sK5) | (spl8_1 | ~spl8_2 | ~spl8_7)),
% 0.21/0.53    inference(resolution,[],[f213,f223])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f114])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5)) ) | (spl8_1 | ~spl8_2 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f212,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f117])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | (spl8_1 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f211,f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f114])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | (spl8_1 | ~spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f167])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    spl8_7 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | spl8_1),
% 0.21/0.53    inference(resolution,[],[f207,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | sP0(X0,X1,X2,X3,X4) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f58,f114])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ~spl8_4 | spl8_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f198])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    $false | (~spl8_4 | spl8_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f197,f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK3,X0,sK4,sK2,sK5)) ) | spl8_7),
% 0.21/0.53    inference(resolution,[],[f169,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f167])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    sP0(sK3,sK6,sK4,sK2,sK5) | (~spl8_4 | spl8_7)),
% 0.21/0.53    inference(resolution,[],[f196,f135])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~sP1(X3,sK2,sK4,X2,sK3) | sP0(sK3,X2,sK4,sK2,X3)) ) | spl8_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f111,f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    v5_pre_topc(sK4,sK2,sK3) | spl8_7),
% 0.21/0.53    inference(subsumption_resolution,[],[f54,f169])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_4 | spl8_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    $false | (~spl8_1 | ~spl8_4 | spl8_6)),
% 0.21/0.53    inference(resolution,[],[f187,f155])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    sP0(sK3,sK6,sK4,sK2,sK5) | (~spl8_1 | ~spl8_4)),
% 0.21/0.53    inference(resolution,[],[f135,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~sP1(X3,sK2,sK4,X2,sK3) | sP0(sK3,X2,sK4,sK2,X3)) ) | ~spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f111,f115])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK3,X0,sK4,sK2,sK5)) ) | spl8_6),
% 0.21/0.53    inference(resolution,[],[f165,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f163])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    spl8_6 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_1 | ~spl8_2 | ~spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f161,f133,f117,f113,f183,f179,f175,f171,f167,f163])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f154,f160])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | (~spl8_1 | ~spl8_4)),
% 0.21/0.53    inference(resolution,[],[f155,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | (~spl8_1 | ~spl8_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f153,f34])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | (~spl8_1 | ~spl8_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f152,f35])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | (~spl8_1 | ~spl8_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f151,f115])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl8_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f36])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl8_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f119])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl8_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    $false | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    v2_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_borsuk_1(sK5,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ~v1_borsuk_1(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    m1_pre_topc(sK5,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ~m1_pre_topc(sK5,sK2) | ~v1_borsuk_1(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v1_borsuk_1(sK6,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ~v1_borsuk_1(sK6,sK2) | ~m1_pre_topc(sK5,sK2) | ~v1_borsuk_1(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    m1_pre_topc(sK6,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ~m1_pre_topc(sK6,sK2) | ~v1_borsuk_1(sK6,sK2) | ~m1_pre_topc(sK5,sK2) | ~v1_borsuk_1(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 0.21/0.53    inference(resolution,[],[f139,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~r4_tsep_1(sK2,sK5,sK6) | spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl8_5 <=> r4_tsep_1(sK2,sK5,sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    spl8_4 | ~spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f131,f137,f133])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~r4_tsep_1(sK2,sK5,sK6) | sP1(sK5,sK2,sK4,sK6,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~v2_struct_0(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~r4_tsep_1(sK2,sK5,sK6) | v2_struct_0(sK5) | sP1(sK5,sK2,sK4,sK6,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f39])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~r4_tsep_1(sK2,sK5,sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | sP1(sK5,sK2,sK4,sK6,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ~v2_struct_0(sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~r4_tsep_1(sK2,sK5,sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | sP1(sK5,sK2,sK4,sK6,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f42])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~r4_tsep_1(sK2,sK5,sK6) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | sP1(sK5,sK2,sK4,sK6,sK3)),
% 0.21/0.53    inference(resolution,[],[f109,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    sQ7_eqProxy(k1_tsep_1(sK2,sK5,sK6),sK2)),
% 0.21/0.53    inference(resolution,[],[f94,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sQ7_eqProxy(X0,X1) | sQ7_eqProxy(X1,X0)) )),
% 0.21/0.53    inference(equality_proxy_axiom,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    sQ7_eqProxy(sK2,k1_tsep_1(sK2,sK5,sK6))),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f43,f93])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK2 = k1_tsep_1(sK2,sK5,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~r4_tsep_1(sK2,X0,X1) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f108,f28])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f107,f29])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f30])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f105,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f104,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f102,f34])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f35])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r4_tsep_1(sK2,X0,X1) | ~sQ7_eqProxy(k1_tsep_1(sK2,X0,X1),sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | sP1(X0,sK2,sK4,X1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(resolution,[],[f36,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~r4_tsep_1(X0,X3,X4) | ~sQ7_eqProxy(k1_tsep_1(X0,X3,X4),X0) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | sP1(X3,X0,X2,X4,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f91,f93])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (sP1(X3,X0,X2,X4,X1) | ~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0 | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X3,X0,X2,X4,X1) | ~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0 | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f8,f12,f11])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) | ~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0 | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) | (~r4_tsep_1(X0,X3,X4) | k1_tsep_1(X0,X3,X4) != X0)) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl8_1 | spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f62,f122,f113])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl8_1 | spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f117,f113])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (8956)------------------------------
% 0.21/0.53  % (8956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8956)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (8956)Memory used [KB]: 11001
% 0.21/0.53  % (8956)Time elapsed: 0.098 s
% 0.21/0.53  % (8956)------------------------------
% 0.21/0.53  % (8956)------------------------------
% 0.21/0.53  % (8952)Success in time 0.168 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:49 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  384 (3142 expanded)
%              Number of leaves         :   33 (1515 expanded)
%              Depth                    :   28
%              Number of atoms          : 3499 (75238 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f148,f167,f178,f205,f228,f292,f324,f360,f369,f391,f412,f433,f454,f488,f503,f510,f540])).

fof(f540,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_5 ),
    inference(subsumption_resolution,[],[f538,f101])).

fof(f101,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl8_1
  <=> v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f538,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_2
    | ~ spl8_4
    | spl8_5 ),
    inference(subsumption_resolution,[],[f537,f105])).

fof(f105,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_2
  <=> v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f537,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_4
    | spl8_5 ),
    inference(subsumption_resolution,[],[f534,f113])).

fof(f113,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_4
  <=> m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f534,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_5 ),
    inference(resolution,[],[f531,f171])).

fof(f171,plain,
    ( ~ sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_5
  <=> sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f531,plain,(
    ! [X1] :
      ( sP1(sK2,sK4,X1,sK5,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f530,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r4_tsep_1(sK2,sK4,sK5)
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f35,f34,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK2,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1)
                          | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                        & r4_tsep_1(sK2,X2,X3)
                        & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                        | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),sK3)
                        | ~ v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5)) )
                      & r4_tsep_1(sK2,X2,X3)
                      & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(X5,X3,sK3)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                  & v5_pre_topc(X4,X2,sK3)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),sK3)
                      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3))
                      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5)) )
                    & r4_tsep_1(sK2,X2,X3)
                    & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,X2,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(X5,X3,sK3)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                & v5_pre_topc(X4,X2,sK3)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_tsep_1(sK2,sK4,X3),sK3)
                    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)) )
                  & r4_tsep_1(sK2,sK4,X3)
                  & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,sK4,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(X5,X3,sK3)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              & v5_pre_topc(X4,sK4,sK3)
              & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_tsep_1(sK2,sK4,X3),sK3)
                  | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3))
                  | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)) )
                & r4_tsep_1(sK2,sK4,X3)
                & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,sK4,X3),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(X5,X3,sK3)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            & v5_pre_topc(X4,sK4,sK3)
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_tsep_1(sK2,sK4,sK5),sK3)
                | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
                | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)) )
              & r4_tsep_1(sK2,sK4,sK5)
              & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X4),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(X5,sK5,sK3)
              & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          & v5_pre_topc(X4,sK4,sK3)
          & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_tsep_1(sK2,sK4,sK5),sK3)
              | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
              | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)) )
            & r4_tsep_1(sK2,sK4,sK5)
            & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X4),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(X5,sK5,sK3)
            & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v5_pre_topc(X4,sK4,sK3)
        & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_tsep_1(sK2,sK4,sK5),sK3)
            | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
            | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)) )
          & r4_tsep_1(sK2,sK4,sK5)
          & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(X5,sK5,sK3)
          & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      & v5_pre_topc(sK6,sK4,sK3)
      & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_tsep_1(sK2,sK4,sK5),sK3)
          | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
          | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)) )
        & r4_tsep_1(sK2,sK4,sK5)
        & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(X5,sK5,sK3)
        & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
        | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
      & r4_tsep_1(sK2,sK4,sK5)
      & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v5_pre_topc(sK7,sK5,sK3)
      & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f11])).

% (30150)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f11,plain,(
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
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X2,X3)
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
                                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ( ~ r1_tsep_1(X2,X3)
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
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_tmap_1)).

fof(f530,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | v2_struct_0(sK3)
      | sP1(sK2,sK4,X1,sK5,sK3) ) ),
    inference(subsumption_resolution,[],[f527,f50])).

fof(f50,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f527,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sP1(sK2,sK4,X1,sK5,sK3) ) ),
    inference(resolution,[],[f525,f51])).

fof(f51,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f524,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f524,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f523,f53])).

fof(f53,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f523,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f522,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f522,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f521,f55])).

fof(f55,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f521,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | ~ m1_pre_topc(sK5,sK2)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_tsep_1(sK2,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3))))
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | sP1(sK2,X1,X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f119,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3))))
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK2,X1,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | sP1(sK2,X1,X0,X2,X3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f47,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3))))
      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK2,X1,X2)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | sP1(sK2,X1,X0,X2,X3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f48,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X0,X2,X4,X3,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
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
    inference(definition_folding,[],[f21,f28,f27])).

fof(f27,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f510,plain,
    ( ~ spl8_23
    | spl8_24 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl8_23
    | spl8_24 ),
    inference(subsumption_resolution,[],[f508,f62])).

fof(f62,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f508,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK3)
    | ~ spl8_23
    | spl8_24 ),
    inference(forward_demodulation,[],[f502,f359])).

fof(f359,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl8_23
  <=> sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f502,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl8_24
  <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f503,plain,
    ( ~ spl8_24
    | ~ spl8_22
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f498,f349,f345,f321,f173,f353,f500])).

fof(f353,plain,
    ( spl8_22
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f173,plain,
    ( spl8_6
  <=> sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f321,plain,
    ( spl8_19
  <=> sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f345,plain,
    ( spl8_20
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f349,plain,
    ( spl8_21
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f498,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f497,f56])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f497,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f496,f323])).

fof(f323,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f321])).

fof(f496,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f495,f57])).

fof(f57,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f495,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f494,f323])).

fof(f494,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f493,f58])).

fof(f58,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f493,plain,
    ( ~ v5_pre_topc(sK6,sK4,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f492,f323])).

fof(f492,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f491,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f491,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f490,f323])).

fof(f490,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f489,f346])).

fof(f346,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f345])).

fof(f489,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f339,f350])).

fof(f350,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f349])).

fof(f339,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_6 ),
    inference(resolution,[],[f175,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
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
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
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
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
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
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f175,plain,
    ( ~ sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f173])).

fof(f488,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f486,f52])).

fof(f486,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f485,f46])).

fof(f485,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f484,f116])).

fof(f116,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f48,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f484,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f483,f54])).

fof(f483,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f482,f55])).

fof(f482,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f481,f53])).

fof(f481,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(duplicate_literal_removal,[],[f480])).

fof(f480,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(resolution,[],[f479,f122])).

fof(f122,plain,(
    ! [X6,X4,X5] :
      ( m1_pre_topc(k1_tsep_1(sK2,X6,X4),X5)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK2)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X4,X5) ) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f121,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK2)
      | v2_struct_0(X6)
      | m1_pre_topc(k1_tsep_1(sK2,X6,X4),X5)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK2)
      | v2_struct_0(X6)
      | m1_pre_topc(k1_tsep_1(sK2,X6,X4),X5)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f479,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f478,f46])).

fof(f478,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f477,f47])).

fof(f477,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f476,f48])).

fof(f476,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f475,f49])).

fof(f475,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f474,f50])).

fof(f474,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f473,f51])).

fof(f473,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f472,f55])).

fof(f472,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f471,f101])).

fof(f471,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f470,f105])).

fof(f470,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_22 ),
    inference(subsumption_resolution,[],[f469,f113])).

fof(f469,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_22 ),
    inference(resolution,[],[f355,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f355,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f353])).

fof(f454,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f452,f52])).

fof(f452,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f451,f46])).

fof(f451,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f450,f116])).

fof(f450,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f449,f54])).

fof(f449,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f448,f55])).

fof(f448,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f447,f53])).

fof(f447,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(resolution,[],[f445,f122])).

fof(f445,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f444,f46])).

fof(f444,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f443,f47])).

fof(f443,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f442,f48])).

fof(f442,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f441,f49])).

fof(f441,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f440,f50])).

fof(f440,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f439,f51])).

fof(f439,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f438,f53])).

fof(f438,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f437,f101])).

fof(f437,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f436,f105])).

fof(f436,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f435,f113])).

fof(f435,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_18 ),
    inference(resolution,[],[f319,f93])).

fof(f319,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl8_18
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f433,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f431,f52])).

fof(f431,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f430,f46])).

fof(f430,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f429,f116])).

fof(f429,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f428,f54])).

fof(f428,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f427,f55])).

fof(f427,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f426,f53])).

fof(f426,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(resolution,[],[f424,f122])).

fof(f424,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f423,f46])).

fof(f423,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f422,f47])).

fof(f422,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f421,f48])).

fof(f421,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f420,f49])).

fof(f420,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f419,f50])).

fof(f419,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f418,f51])).

fof(f418,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f417,f55])).

fof(f417,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f416,f101])).

fof(f416,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f415,f105])).

fof(f415,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_21 ),
    inference(subsumption_resolution,[],[f414,f113])).

fof(f414,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_21 ),
    inference(resolution,[],[f351,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f25])).

fof(f351,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_21 ),
    inference(avatar_component_clause,[],[f349])).

fof(f412,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f410,f52])).

fof(f410,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f409,f46])).

fof(f409,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f408,f116])).

fof(f408,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f407,f54])).

fof(f407,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f406,f55])).

fof(f406,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f405,f53])).

fof(f405,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(resolution,[],[f403,f122])).

fof(f403,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f402,f46])).

fof(f402,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f401,f47])).

fof(f401,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f400,f48])).

fof(f400,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f399,f49])).

fof(f399,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f398,f50])).

fof(f398,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f397,f51])).

fof(f397,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f396,f53])).

fof(f396,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f395,f101])).

fof(f395,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f394,f105])).

fof(f394,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f393,f113])).

fof(f393,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_17 ),
    inference(resolution,[],[f315,f92])).

fof(f315,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl8_17
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f391,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f389,f52])).

fof(f389,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f388,f46])).

fof(f388,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f387,f116])).

fof(f387,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f386,f54])).

fof(f386,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f385,f55])).

fof(f385,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f384,f53])).

fof(f384,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(resolution,[],[f382,f122])).

fof(f382,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f381,f46])).

fof(f381,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f380,f47])).

fof(f380,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f379,f48])).

fof(f379,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f378,f49])).

fof(f378,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f377,f50])).

fof(f377,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f376,f51])).

fof(f376,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f375,f55])).

fof(f375,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f374,f101])).

fof(f374,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f373,f105])).

fof(f373,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f371,f113])).

fof(f371,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_20 ),
    inference(resolution,[],[f347,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f25])).

fof(f347,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f345])).

fof(f369,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f367,f52])).

fof(f367,plain,
    ( v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f366,f46])).

fof(f366,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f365,f116])).

fof(f365,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f364,f54])).

fof(f364,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f363,f55])).

fof(f363,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f362,f53])).

fof(f362,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(resolution,[],[f122,f338])).

fof(f338,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f337,f46])).

fof(f337,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f336,f47])).

fof(f336,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f335,f48])).

fof(f335,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f334,f49])).

fof(f334,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f333,f50])).

fof(f333,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f332,f51])).

fof(f332,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f331,f53])).

fof(f331,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f330,f101])).

fof(f330,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f329,f105])).

fof(f329,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_16 ),
    inference(subsumption_resolution,[],[f326,f113])).

fof(f326,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_16 ),
    inference(resolution,[],[f311,f91])).

fof(f311,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl8_16
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f360,plain,
    ( ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | spl8_23
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f343,f225,f357,f353,f349,f345])).

fof(f225,plain,
    ( spl8_8
  <=> r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f343,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f342,f60])).

fof(f60,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f342,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f341,f61])).

fof(f61,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f341,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f340,f63])).

fof(f63,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f340,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_8 ),
    inference(resolution,[],[f227,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f227,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f225])).

fof(f324,plain,
    ( ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | spl8_19
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f307,f202,f321,f317,f313,f309])).

fof(f202,plain,
    ( spl8_7
  <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f307,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f306,f56])).

fof(f306,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f305,f57])).

fof(f305,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f304,f59])).

fof(f304,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_7 ),
    inference(resolution,[],[f204,f89])).

fof(f204,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f202])).

fof(f292,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f290,f46])).

fof(f290,plain,
    ( v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f289,f47])).

fof(f289,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f288,f48])).

fof(f288,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f287,f49])).

fof(f287,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f286,f50])).

fof(f286,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f285,f51])).

% (30136)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f285,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f284,f52])).

fof(f284,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f283,f53])).

fof(f283,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f282,f54])).

fof(f282,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f281,f55])).

fof(f281,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f280,f56])).

fof(f280,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f279,f57])).

fof(f279,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f278,f59])).

fof(f278,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f277,f60])).

fof(f277,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f276,f61])).

fof(f276,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f274,f63])).

fof(f274,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f114,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f228,plain,
    ( spl8_8
    | ~ spl8_4
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f223,f104,f100,f112,f225])).

fof(f223,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f222,f46])).

fof(f222,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f221,f47])).

fof(f221,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f220,f48])).

fof(f220,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f219,f49])).

fof(f219,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f218,f50])).

fof(f218,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f217,f51])).

fof(f217,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f216,f52])).

fof(f216,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f215,f53])).

fof(f215,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f214,f54])).

fof(f214,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f213,f55])).

fof(f213,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f212,f56])).

fof(f212,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f211,f57])).

fof(f211,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f210,f59])).

fof(f210,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f209,f60])).

fof(f209,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f207,f63])).

fof(f207,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f206,f101])).

fof(f206,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f180,f105])).

fof(f180,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
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
    inference(resolution,[],[f64,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
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
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f19])).

% (30148)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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

fof(f10,plain,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).

fof(f64,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f36])).

fof(f205,plain,
    ( spl8_7
    | ~ spl8_4
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f200,f104,f100,f112,f202])).

fof(f200,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f199,f46])).

fof(f199,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f198,f47])).

fof(f198,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f197,f48])).

fof(f197,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f196,f49])).

fof(f196,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f195,f50])).

fof(f195,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f194,f51])).

fof(f194,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f193,f52])).

fof(f193,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f192,f53])).

fof(f192,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f191,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f190,f55])).

fof(f190,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f189,f56])).

fof(f189,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f188,f57])).

fof(f188,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f187,f59])).

fof(f187,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f186,f60])).

fof(f186,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f185,f61])).

fof(f185,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f184,f63])).

fof(f184,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f183,f101])).

fof(f183,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f179,f105])).

fof(f179,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
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
    inference(resolution,[],[f64,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
    inference(cnf_transformation,[],[f38])).

fof(f178,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | spl8_3 ),
    inference(avatar_split_clause,[],[f177,f108,f173,f169])).

fof(f108,plain,
    ( spl8_3
  <=> v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f177,plain,
    ( ~ sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | ~ sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | spl8_3 ),
    inference(resolution,[],[f110,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f110,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f167,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f165,f46])).

fof(f165,plain,
    ( v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f164,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f163,f48])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f162,f49])).

fof(f162,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f161,f50])).

fof(f161,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f160,f51])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f159,f52])).

fof(f159,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f158,f53])).

fof(f158,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f157,f54])).

fof(f157,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f156,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f155,f56])).

fof(f155,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f154,f57])).

fof(f154,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f153,f59])).

fof(f153,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f152,f60])).

fof(f152,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f151,f61])).

fof(f151,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(resolution,[],[f106,f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f148,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f146,f46])).

fof(f146,plain,
    ( v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f144,f48])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f143,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f142,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f141,f51])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f140,f52])).

fof(f140,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f139,f53])).

fof(f139,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f138,f54])).

fof(f138,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f137,f55])).

fof(f137,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f136,f56])).

fof(f136,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f135,f57])).

fof(f135,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f134,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f133,f60])).

fof(f133,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f132,f61])).

fof(f132,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f130,f63])).

fof(f130,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f115,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f66,f112,f108,f104,f100])).

fof(f66,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (30141)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.47  % (30133)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (30127)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (30134)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (30147)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (30139)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (30143)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (30129)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (30131)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (30125)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (30126)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (30138)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (30132)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (30130)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (30128)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (30149)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (30142)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (30135)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (30145)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (30146)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (30140)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.35/0.53  % (30137)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.35/0.53  % (30144)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.35/0.54  % (30131)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f541,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(avatar_sat_refutation,[],[f115,f148,f167,f178,f205,f228,f292,f324,f360,f369,f391,f412,f433,f454,f488,f503,f510,f540])).
% 1.35/0.54  fof(f540,plain,(
% 1.35/0.54    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_5),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f539])).
% 1.35/0.54  fof(f539,plain,(
% 1.35/0.54    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_5)),
% 1.35/0.54    inference(subsumption_resolution,[],[f538,f101])).
% 1.35/0.54  fof(f101,plain,(
% 1.35/0.54    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_1),
% 1.35/0.54    inference(avatar_component_clause,[],[f100])).
% 1.35/0.54  fof(f100,plain,(
% 1.35/0.54    spl8_1 <=> v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.35/0.54  fof(f538,plain,(
% 1.35/0.54    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | (~spl8_2 | ~spl8_4 | spl8_5)),
% 1.35/0.54    inference(subsumption_resolution,[],[f537,f105])).
% 1.35/0.54  fof(f105,plain,(
% 1.35/0.54    v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~spl8_2),
% 1.35/0.54    inference(avatar_component_clause,[],[f104])).
% 1.35/0.54  fof(f104,plain,(
% 1.35/0.54    spl8_2 <=> v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.35/0.54  fof(f537,plain,(
% 1.35/0.54    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | (~spl8_4 | spl8_5)),
% 1.35/0.54    inference(subsumption_resolution,[],[f534,f113])).
% 1.35/0.54  fof(f113,plain,(
% 1.35/0.54    m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~spl8_4),
% 1.35/0.54    inference(avatar_component_clause,[],[f112])).
% 1.35/0.54  fof(f112,plain,(
% 1.35/0.54    spl8_4 <=> m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.35/0.54  fof(f534,plain,(
% 1.35/0.54    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_5),
% 1.35/0.54    inference(resolution,[],[f531,f171])).
% 1.35/0.54  fof(f171,plain,(
% 1.35/0.54    ~sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | spl8_5),
% 1.35/0.54    inference(avatar_component_clause,[],[f169])).
% 1.35/0.54  fof(f169,plain,(
% 1.35/0.54    spl8_5 <=> sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.35/0.54  fof(f531,plain,(
% 1.35/0.54    ( ! [X1] : (sP1(sK2,sK4,X1,sK5,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(X1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f530,f49])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    ~v2_struct_0(sK3)),
% 1.35/0.54    inference(cnf_transformation,[],[f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f35,f34,f33,f32,f31,f30])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f31,plain,(
% 1.46/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f32,plain,(
% 1.46/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_tsep_1(sK2,sK4,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5))) & r4_tsep_1(sK2,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f33,plain,(
% 1.46/0.54    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_tsep_1(sK2,sK4,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5))) & r4_tsep_1(sK2,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X4),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f34,plain,(
% 1.46/0.54    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X4),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f35,plain,(
% 1.46/0.54    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7))),
% 1.46/0.54    introduced(choice_axiom,[])).
% 1.46/0.54  fof(f13,plain,(
% 1.46/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.46/0.54    inference(flattening,[],[f12])).
% 1.46/0.54  fof(f12,plain,(
% 1.46/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.46/0.54    inference(ennf_transformation,[],[f11])).
% 1.46/0.54  % (30150)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.46/0.54  fof(f11,plain,(
% 1.46/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.46/0.54    inference(pure_predicate_removal,[],[f9])).
% 1.46/0.54  fof(f9,negated_conjecture,(
% 1.46/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 1.46/0.54    inference(negated_conjecture,[],[f8])).
% 1.46/0.54  fof(f8,conjecture,(
% 1.46/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 1.46/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_tmap_1)).
% 1.46/0.54  fof(f530,plain,(
% 1.46/0.54    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | v2_struct_0(sK3) | sP1(sK2,sK4,X1,sK5,sK3)) )),
% 1.46/0.54    inference(subsumption_resolution,[],[f527,f50])).
% 1.46/0.54  fof(f50,plain,(
% 1.46/0.54    v2_pre_topc(sK3)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.54  fof(f527,plain,(
% 1.46/0.54    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sP1(sK2,sK4,X1,sK5,sK3)) )),
% 1.46/0.54    inference(resolution,[],[f525,f51])).
% 1.46/0.54  fof(f51,plain,(
% 1.46/0.54    l1_pre_topc(sK3)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.54  fof(f525,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 1.46/0.54    inference(subsumption_resolution,[],[f524,f52])).
% 1.46/0.54  fof(f52,plain,(
% 1.46/0.54    ~v2_struct_0(sK4)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.54  fof(f524,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 1.46/0.54    inference(subsumption_resolution,[],[f523,f53])).
% 1.46/0.54  fof(f53,plain,(
% 1.46/0.54    m1_pre_topc(sK4,sK2)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.54  fof(f523,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 1.46/0.54    inference(subsumption_resolution,[],[f522,f54])).
% 1.46/0.54  fof(f54,plain,(
% 1.46/0.54    ~v2_struct_0(sK5)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.54  fof(f522,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 1.46/0.54    inference(subsumption_resolution,[],[f521,f55])).
% 1.46/0.54  fof(f55,plain,(
% 1.46/0.54    m1_pre_topc(sK5,sK2)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.54  fof(f521,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 1.46/0.54    inference(resolution,[],[f120,f65])).
% 1.46/0.54  fof(f65,plain,(
% 1.46/0.54    r4_tsep_1(sK2,sK4,sK5)),
% 1.46/0.54    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f120,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r4_tsep_1(sK2,X1,X2) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)))) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | sP1(sK2,X1,X0,X2,X3)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f119,f46])).
% 1.46/0.55  fof(f46,plain,(
% 1.46/0.55    ~v2_struct_0(sK2)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f119,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK2,X1,X2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | sP1(sK2,X1,X0,X2,X3) | v2_struct_0(sK2)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f117,f47])).
% 1.46/0.55  fof(f47,plain,(
% 1.46/0.55    v2_pre_topc(sK2)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f117,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK2,X1,X2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | sP1(sK2,X1,X0,X2,X3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.46/0.55    inference(resolution,[],[f48,f88])).
% 1.46/0.55  fof(f88,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X0,X2,X4,X3,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(definition_folding,[],[f21,f28,f27])).
% 1.46/0.55  fof(f27,plain,(
% 1.46/0.55    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 1.46/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 1.46/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(flattening,[],[f20])).
% 1.46/0.55  fof(f20,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f5])).
% 1.46/0.55  fof(f5,axiom,(
% 1.46/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 1.46/0.55  fof(f48,plain,(
% 1.46/0.55    l1_pre_topc(sK2)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f510,plain,(
% 1.46/0.55    ~spl8_23 | spl8_24),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f509])).
% 1.46/0.55  fof(f509,plain,(
% 1.46/0.55    $false | (~spl8_23 | spl8_24)),
% 1.46/0.55    inference(subsumption_resolution,[],[f508,f62])).
% 1.46/0.55  fof(f62,plain,(
% 1.46/0.55    v5_pre_topc(sK7,sK5,sK3)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f508,plain,(
% 1.46/0.55    ~v5_pre_topc(sK7,sK5,sK3) | (~spl8_23 | spl8_24)),
% 1.46/0.55    inference(forward_demodulation,[],[f502,f359])).
% 1.46/0.55  fof(f359,plain,(
% 1.46/0.55    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_23),
% 1.46/0.55    inference(avatar_component_clause,[],[f357])).
% 1.46/0.55  fof(f357,plain,(
% 1.46/0.55    spl8_23 <=> sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.46/0.55  fof(f502,plain,(
% 1.46/0.55    ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | spl8_24),
% 1.46/0.55    inference(avatar_component_clause,[],[f500])).
% 1.46/0.55  fof(f500,plain,(
% 1.46/0.55    spl8_24 <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.46/0.55  fof(f503,plain,(
% 1.46/0.55    ~spl8_24 | ~spl8_22 | spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21),
% 1.46/0.55    inference(avatar_split_clause,[],[f498,f349,f345,f321,f173,f353,f500])).
% 1.46/0.55  fof(f353,plain,(
% 1.46/0.55    spl8_22 <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.46/0.55  fof(f173,plain,(
% 1.46/0.55    spl8_6 <=> sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.46/0.55  fof(f321,plain,(
% 1.46/0.55    spl8_19 <=> sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.46/0.55  fof(f345,plain,(
% 1.46/0.55    spl8_20 <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.46/0.55  fof(f349,plain,(
% 1.46/0.55    spl8_21 <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.46/0.55  fof(f498,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f497,f56])).
% 1.46/0.55  fof(f56,plain,(
% 1.46/0.55    v1_funct_1(sK6)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f497,plain,(
% 1.46/0.55    ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(forward_demodulation,[],[f496,f323])).
% 1.46/0.55  fof(f323,plain,(
% 1.46/0.55    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_19),
% 1.46/0.55    inference(avatar_component_clause,[],[f321])).
% 1.46/0.55  fof(f496,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f495,f57])).
% 1.46/0.55  fof(f57,plain,(
% 1.46/0.55    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f495,plain,(
% 1.46/0.55    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(forward_demodulation,[],[f494,f323])).
% 1.46/0.55  fof(f494,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f493,f58])).
% 1.46/0.55  fof(f58,plain,(
% 1.46/0.55    v5_pre_topc(sK6,sK4,sK3)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f493,plain,(
% 1.46/0.55    ~v5_pre_topc(sK6,sK4,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(forward_demodulation,[],[f492,f323])).
% 1.46/0.55  fof(f492,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f491,f59])).
% 1.46/0.55  fof(f59,plain,(
% 1.46/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f491,plain,(
% 1.46/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(forward_demodulation,[],[f490,f323])).
% 1.46/0.55  fof(f490,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_20 | ~spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f489,f346])).
% 1.46/0.55  fof(f346,plain,(
% 1.46/0.55    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_20),
% 1.46/0.55    inference(avatar_component_clause,[],[f345])).
% 1.46/0.55  fof(f489,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_6 | ~spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f339,f350])).
% 1.46/0.55  fof(f350,plain,(
% 1.46/0.55    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl8_21),
% 1.46/0.55    inference(avatar_component_clause,[],[f349])).
% 1.46/0.55  fof(f339,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | spl8_6),
% 1.46/0.55    inference(resolution,[],[f175,f87])).
% 1.46/0.55  fof(f87,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f44])).
% 1.46/0.55  fof(f44,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.46/0.55    inference(rectify,[],[f43])).
% 1.46/0.55  fof(f43,plain,(
% 1.46/0.55    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 1.46/0.55    inference(flattening,[],[f42])).
% 1.46/0.55  fof(f42,plain,(
% 1.46/0.55    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 1.46/0.55    inference(nnf_transformation,[],[f27])).
% 1.46/0.55  fof(f175,plain,(
% 1.46/0.55    ~sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | spl8_6),
% 1.46/0.55    inference(avatar_component_clause,[],[f173])).
% 1.46/0.55  fof(f488,plain,(
% 1.46/0.55    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f487])).
% 1.46/0.55  fof(f487,plain,(
% 1.46/0.55    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f486,f52])).
% 1.46/0.55  fof(f486,plain,(
% 1.46/0.55    v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f485,f46])).
% 1.46/0.55  fof(f485,plain,(
% 1.46/0.55    v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f484,f116])).
% 1.46/0.55  fof(f116,plain,(
% 1.46/0.55    m1_pre_topc(sK2,sK2)),
% 1.46/0.55    inference(resolution,[],[f48,f94])).
% 1.46/0.55  fof(f94,plain,(
% 1.46/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f26])).
% 1.46/0.55  fof(f26,plain,(
% 1.46/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.46/0.55    inference(ennf_transformation,[],[f7])).
% 1.46/0.55  fof(f7,axiom,(
% 1.46/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.46/0.55  fof(f484,plain,(
% 1.46/0.55    ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f483,f54])).
% 1.46/0.55  fof(f483,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f482,f55])).
% 1.46/0.55  fof(f482,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f481,f53])).
% 1.46/0.55  fof(f481,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f480])).
% 1.46/0.55  fof(f480,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(resolution,[],[f479,f122])).
% 1.46/0.55  fof(f122,plain,(
% 1.46/0.55    ( ! [X6,X4,X5] : (m1_pre_topc(k1_tsep_1(sK2,X6,X4),X5) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK2) | v2_struct_0(X6) | ~m1_pre_topc(X4,X5)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f121,f46])).
% 1.46/0.55  fof(f121,plain,(
% 1.46/0.55    ( ! [X6,X4,X5] : (~m1_pre_topc(X4,X5) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK2) | v2_struct_0(X6) | m1_pre_topc(k1_tsep_1(sK2,X6,X4),X5) | v2_struct_0(sK2)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f118,f47])).
% 1.46/0.55  fof(f118,plain,(
% 1.46/0.55    ( ! [X6,X4,X5] : (~m1_pre_topc(X4,X5) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK2) | v2_struct_0(X6) | m1_pre_topc(k1_tsep_1(sK2,X6,X4),X5) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.46/0.55    inference(resolution,[],[f48,f67])).
% 1.46/0.55  fof(f67,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f15])).
% 1.46/0.55  fof(f15,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(flattening,[],[f14])).
% 1.46/0.55  fof(f14,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | (~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f6])).
% 1.46/0.55  fof(f6,axiom,(
% 1.46/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).
% 1.46/0.55  fof(f479,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f478,f46])).
% 1.46/0.55  fof(f478,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f477,f47])).
% 1.46/0.55  fof(f477,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f476,f48])).
% 1.46/0.55  fof(f476,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f475,f49])).
% 1.46/0.55  fof(f475,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f474,f50])).
% 1.46/0.55  fof(f474,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f473,f51])).
% 1.46/0.55  fof(f473,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f472,f55])).
% 1.46/0.55  fof(f472,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f471,f101])).
% 1.46/0.55  fof(f471,plain,(
% 1.46/0.55    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f470,f105])).
% 1.46/0.55  fof(f470,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_22)),
% 1.46/0.55    inference(subsumption_resolution,[],[f469,f113])).
% 1.46/0.55  fof(f469,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_22),
% 1.46/0.55    inference(resolution,[],[f355,f93])).
% 1.46/0.55  fof(f93,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(flattening,[],[f24])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f4])).
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.46/0.55  fof(f355,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_22),
% 1.46/0.55    inference(avatar_component_clause,[],[f353])).
% 1.46/0.55  fof(f454,plain,(
% 1.46/0.55    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f453])).
% 1.46/0.55  fof(f453,plain,(
% 1.46/0.55    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f452,f52])).
% 1.46/0.55  fof(f452,plain,(
% 1.46/0.55    v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f451,f46])).
% 1.46/0.55  fof(f451,plain,(
% 1.46/0.55    v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f450,f116])).
% 1.46/0.55  fof(f450,plain,(
% 1.46/0.55    ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f449,f54])).
% 1.46/0.55  fof(f449,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f448,f55])).
% 1.46/0.55  fof(f448,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f447,f53])).
% 1.46/0.55  fof(f447,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f446])).
% 1.46/0.55  fof(f446,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(resolution,[],[f445,f122])).
% 1.46/0.55  fof(f445,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f444,f46])).
% 1.46/0.55  fof(f444,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f443,f47])).
% 1.46/0.55  fof(f443,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f442,f48])).
% 1.46/0.55  fof(f442,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f441,f49])).
% 1.46/0.55  fof(f441,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f440,f50])).
% 1.46/0.55  fof(f440,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f439,f51])).
% 1.46/0.55  fof(f439,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f438,f53])).
% 1.46/0.55  fof(f438,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f437,f101])).
% 1.46/0.55  fof(f437,plain,(
% 1.46/0.55    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f436,f105])).
% 1.46/0.55  fof(f436,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_18)),
% 1.46/0.55    inference(subsumption_resolution,[],[f435,f113])).
% 1.46/0.55  fof(f435,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_18),
% 1.46/0.55    inference(resolution,[],[f319,f93])).
% 1.46/0.55  fof(f319,plain,(
% 1.46/0.55    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | spl8_18),
% 1.46/0.55    inference(avatar_component_clause,[],[f317])).
% 1.46/0.55  fof(f317,plain,(
% 1.46/0.55    spl8_18 <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.46/0.55  fof(f433,plain,(
% 1.46/0.55    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f432])).
% 1.46/0.55  fof(f432,plain,(
% 1.46/0.55    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f431,f52])).
% 1.46/0.55  fof(f431,plain,(
% 1.46/0.55    v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f430,f46])).
% 1.46/0.55  fof(f430,plain,(
% 1.46/0.55    v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f429,f116])).
% 1.46/0.55  fof(f429,plain,(
% 1.46/0.55    ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f428,f54])).
% 1.46/0.55  fof(f428,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f427,f55])).
% 1.46/0.55  fof(f427,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f426,f53])).
% 1.46/0.55  fof(f426,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f425])).
% 1.46/0.55  fof(f425,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(resolution,[],[f424,f122])).
% 1.46/0.55  fof(f424,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f423,f46])).
% 1.46/0.55  fof(f423,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f422,f47])).
% 1.46/0.55  fof(f422,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f421,f48])).
% 1.46/0.55  fof(f421,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f420,f49])).
% 1.46/0.55  fof(f420,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f419,f50])).
% 1.46/0.55  fof(f419,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f418,f51])).
% 1.46/0.55  fof(f418,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f417,f55])).
% 1.46/0.55  fof(f417,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f416,f101])).
% 1.46/0.55  fof(f416,plain,(
% 1.46/0.55    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f415,f105])).
% 1.46/0.55  fof(f415,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_21)),
% 1.46/0.55    inference(subsumption_resolution,[],[f414,f113])).
% 1.46/0.55  fof(f414,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_21),
% 1.46/0.55    inference(resolution,[],[f351,f92])).
% 1.46/0.55  fof(f92,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f351,plain,(
% 1.46/0.55    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | spl8_21),
% 1.46/0.55    inference(avatar_component_clause,[],[f349])).
% 1.46/0.55  fof(f412,plain,(
% 1.46/0.55    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f411])).
% 1.46/0.55  fof(f411,plain,(
% 1.46/0.55    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f410,f52])).
% 1.46/0.55  fof(f410,plain,(
% 1.46/0.55    v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f409,f46])).
% 1.46/0.55  fof(f409,plain,(
% 1.46/0.55    v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f408,f116])).
% 1.46/0.55  fof(f408,plain,(
% 1.46/0.55    ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f407,f54])).
% 1.46/0.55  fof(f407,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f406,f55])).
% 1.46/0.55  fof(f406,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f405,f53])).
% 1.46/0.55  fof(f405,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f404])).
% 1.46/0.55  fof(f404,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(resolution,[],[f403,f122])).
% 1.46/0.55  fof(f403,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f402,f46])).
% 1.46/0.55  fof(f402,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f401,f47])).
% 1.46/0.55  fof(f401,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f400,f48])).
% 1.46/0.55  fof(f400,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f399,f49])).
% 1.46/0.55  fof(f399,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f398,f50])).
% 1.46/0.55  fof(f398,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f397,f51])).
% 1.46/0.55  fof(f397,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f396,f53])).
% 1.46/0.55  fof(f396,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f395,f101])).
% 1.46/0.55  fof(f395,plain,(
% 1.46/0.55    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f394,f105])).
% 1.46/0.55  fof(f394,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_17)),
% 1.46/0.55    inference(subsumption_resolution,[],[f393,f113])).
% 1.46/0.55  fof(f393,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_17),
% 1.46/0.55    inference(resolution,[],[f315,f92])).
% 1.46/0.55  fof(f315,plain,(
% 1.46/0.55    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | spl8_17),
% 1.46/0.55    inference(avatar_component_clause,[],[f313])).
% 1.46/0.55  fof(f313,plain,(
% 1.46/0.55    spl8_17 <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.46/0.55  fof(f391,plain,(
% 1.46/0.55    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f390])).
% 1.46/0.55  fof(f390,plain,(
% 1.46/0.55    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f389,f52])).
% 1.46/0.55  fof(f389,plain,(
% 1.46/0.55    v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f388,f46])).
% 1.46/0.55  fof(f388,plain,(
% 1.46/0.55    v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f387,f116])).
% 1.46/0.55  fof(f387,plain,(
% 1.46/0.55    ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f386,f54])).
% 1.46/0.55  fof(f386,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f385,f55])).
% 1.46/0.55  fof(f385,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f384,f53])).
% 1.46/0.55  fof(f384,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f383])).
% 1.46/0.55  fof(f383,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(resolution,[],[f382,f122])).
% 1.46/0.55  fof(f382,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f381,f46])).
% 1.46/0.55  fof(f381,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f380,f47])).
% 1.46/0.55  fof(f380,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f379,f48])).
% 1.46/0.55  fof(f379,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f378,f49])).
% 1.46/0.55  fof(f378,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f377,f50])).
% 1.46/0.55  fof(f377,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f376,f51])).
% 1.46/0.55  fof(f376,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f375,f55])).
% 1.46/0.55  fof(f375,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f374,f101])).
% 1.46/0.55  fof(f374,plain,(
% 1.46/0.55    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f373,f105])).
% 1.46/0.55  fof(f373,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_20)),
% 1.46/0.55    inference(subsumption_resolution,[],[f371,f113])).
% 1.46/0.55  fof(f371,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_20),
% 1.46/0.55    inference(resolution,[],[f347,f91])).
% 1.46/0.55  fof(f91,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f347,plain,(
% 1.46/0.55    ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | spl8_20),
% 1.46/0.55    inference(avatar_component_clause,[],[f345])).
% 1.46/0.55  fof(f369,plain,(
% 1.46/0.55    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f368])).
% 1.46/0.55  fof(f368,plain,(
% 1.46/0.55    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f367,f52])).
% 1.46/0.55  fof(f367,plain,(
% 1.46/0.55    v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f366,f46])).
% 1.46/0.55  fof(f366,plain,(
% 1.46/0.55    v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f365,f116])).
% 1.46/0.55  fof(f365,plain,(
% 1.46/0.55    ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f364,f54])).
% 1.46/0.55  fof(f364,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f363,f55])).
% 1.46/0.55  fof(f363,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f362,f53])).
% 1.46/0.55  fof(f362,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | v2_struct_0(sK4) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f361])).
% 1.46/0.55  fof(f361,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(resolution,[],[f122,f338])).
% 1.46/0.55  fof(f338,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f337,f46])).
% 1.46/0.55  fof(f337,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f336,f47])).
% 1.46/0.55  fof(f336,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f335,f48])).
% 1.46/0.55  fof(f335,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f334,f49])).
% 1.46/0.55  fof(f334,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f333,f50])).
% 1.46/0.55  fof(f333,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f332,f51])).
% 1.46/0.55  fof(f332,plain,(
% 1.46/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f331,f53])).
% 1.46/0.55  fof(f331,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f330,f101])).
% 1.46/0.55  fof(f330,plain,(
% 1.46/0.55    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f329,f105])).
% 1.46/0.55  fof(f329,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_16)),
% 1.46/0.55    inference(subsumption_resolution,[],[f326,f113])).
% 1.46/0.55  fof(f326,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_16),
% 1.46/0.55    inference(resolution,[],[f311,f91])).
% 1.46/0.55  fof(f311,plain,(
% 1.46/0.55    ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | spl8_16),
% 1.46/0.55    inference(avatar_component_clause,[],[f309])).
% 1.46/0.55  fof(f309,plain,(
% 1.46/0.55    spl8_16 <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.46/0.55  fof(f360,plain,(
% 1.46/0.55    ~spl8_20 | ~spl8_21 | ~spl8_22 | spl8_23 | ~spl8_8),
% 1.46/0.55    inference(avatar_split_clause,[],[f343,f225,f357,f353,f349,f345])).
% 1.46/0.55  fof(f225,plain,(
% 1.46/0.55    spl8_8 <=> r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.46/0.55  fof(f343,plain,(
% 1.46/0.55    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_8),
% 1.46/0.55    inference(subsumption_resolution,[],[f342,f60])).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    v1_funct_1(sK7)),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f342,plain,(
% 1.46/0.55    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_1(sK7) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_8),
% 1.46/0.55    inference(subsumption_resolution,[],[f341,f61])).
% 1.46/0.55  fof(f61,plain,(
% 1.46/0.55    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f341,plain,(
% 1.46/0.55    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_8),
% 1.46/0.55    inference(subsumption_resolution,[],[f340,f63])).
% 1.46/0.55  fof(f63,plain,(
% 1.46/0.55    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f340,plain,(
% 1.46/0.55    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_8),
% 1.46/0.55    inference(resolution,[],[f227,f89])).
% 1.46/0.55  fof(f89,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f45])).
% 1.46/0.55  fof(f45,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.55    inference(nnf_transformation,[],[f23])).
% 1.46/0.55  fof(f23,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.55    inference(flattening,[],[f22])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.55    inference(ennf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.46/0.55  fof(f227,plain,(
% 1.46/0.55    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~spl8_8),
% 1.46/0.55    inference(avatar_component_clause,[],[f225])).
% 1.46/0.55  fof(f324,plain,(
% 1.46/0.55    ~spl8_16 | ~spl8_17 | ~spl8_18 | spl8_19 | ~spl8_7),
% 1.46/0.55    inference(avatar_split_clause,[],[f307,f202,f321,f317,f313,f309])).
% 1.46/0.55  fof(f202,plain,(
% 1.46/0.55    spl8_7 <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.46/0.55  fof(f307,plain,(
% 1.46/0.55    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_7),
% 1.46/0.55    inference(subsumption_resolution,[],[f306,f56])).
% 1.46/0.55  fof(f306,plain,(
% 1.46/0.55    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_7),
% 1.46/0.55    inference(subsumption_resolution,[],[f305,f57])).
% 1.46/0.55  fof(f305,plain,(
% 1.46/0.55    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_7),
% 1.46/0.55    inference(subsumption_resolution,[],[f304,f59])).
% 1.46/0.55  fof(f304,plain,(
% 1.46/0.55    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_7),
% 1.46/0.55    inference(resolution,[],[f204,f89])).
% 1.46/0.55  fof(f204,plain,(
% 1.46/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~spl8_7),
% 1.46/0.55    inference(avatar_component_clause,[],[f202])).
% 1.46/0.55  fof(f292,plain,(
% 1.46/0.55    spl8_4),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f291])).
% 1.46/0.55  fof(f291,plain,(
% 1.46/0.55    $false | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f290,f46])).
% 1.46/0.55  fof(f290,plain,(
% 1.46/0.55    v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f289,f47])).
% 1.46/0.55  fof(f289,plain,(
% 1.46/0.55    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f288,f48])).
% 1.46/0.55  fof(f288,plain,(
% 1.46/0.55    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f287,f49])).
% 1.46/0.55  fof(f287,plain,(
% 1.46/0.55    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f286,f50])).
% 1.46/0.55  fof(f286,plain,(
% 1.46/0.55    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f285,f51])).
% 1.46/0.55  % (30136)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.46/0.55  fof(f285,plain,(
% 1.46/0.55    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f284,f52])).
% 1.46/0.55  fof(f284,plain,(
% 1.46/0.55    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f283,f53])).
% 1.46/0.55  fof(f283,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f282,f54])).
% 1.46/0.55  fof(f282,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f281,f55])).
% 1.46/0.55  fof(f281,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f280,f56])).
% 1.46/0.55  fof(f280,plain,(
% 1.46/0.55    ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f279,f57])).
% 1.46/0.55  fof(f279,plain,(
% 1.46/0.55    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f278,f59])).
% 1.46/0.55  fof(f278,plain,(
% 1.46/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f277,f60])).
% 1.46/0.55  fof(f277,plain,(
% 1.46/0.55    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f276,f61])).
% 1.46/0.55  fof(f276,plain,(
% 1.46/0.55    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(subsumption_resolution,[],[f274,f63])).
% 1.46/0.55  fof(f274,plain,(
% 1.46/0.55    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.46/0.55    inference(resolution,[],[f114,f70])).
% 1.46/0.55  fof(f70,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f17])).
% 1.46/0.55  fof(f17,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(flattening,[],[f16])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f3])).
% 1.46/0.55  fof(f3,axiom,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.46/0.55  fof(f114,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | spl8_4),
% 1.46/0.55    inference(avatar_component_clause,[],[f112])).
% 1.46/0.55  fof(f228,plain,(
% 1.46/0.55    spl8_8 | ~spl8_4 | ~spl8_1 | ~spl8_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f223,f104,f100,f112,f225])).
% 1.46/0.55  fof(f223,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f222,f46])).
% 1.46/0.55  fof(f222,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f221,f47])).
% 1.46/0.55  fof(f221,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f220,f48])).
% 1.46/0.55  fof(f220,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f219,f49])).
% 1.46/0.55  fof(f219,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f218,f50])).
% 1.46/0.55  fof(f218,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f217,f51])).
% 1.46/0.55  fof(f217,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f216,f52])).
% 1.46/0.55  fof(f216,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f215,f53])).
% 1.46/0.55  fof(f215,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f214,f54])).
% 1.46/0.55  fof(f214,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f213,f55])).
% 1.46/0.55  fof(f213,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f212,f56])).
% 1.46/0.55  fof(f212,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f211,f57])).
% 1.46/0.55  fof(f211,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f210,f59])).
% 1.46/0.55  fof(f210,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f209,f60])).
% 1.46/0.55  fof(f209,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f208,f61])).
% 1.46/0.55  fof(f208,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f207,f63])).
% 1.46/0.55  fof(f207,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f206,f101])).
% 1.46/0.55  fof(f206,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f180,f105])).
% 1.46/0.55  fof(f180,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.46/0.55    inference(resolution,[],[f64,f95])).
% 1.46/0.55  fof(f95,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(equality_resolution,[],[f72])).
% 1.46/0.55  fof(f72,plain,(
% 1.46/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f38])).
% 1.46/0.55  fof(f38,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(flattening,[],[f37])).
% 1.46/0.55  fof(f37,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(nnf_transformation,[],[f19])).
% 1.46/0.55  % (30148)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.46/0.55  fof(f19,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.55    inference(flattening,[],[f18])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6))) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f10])).
% 1.46/0.55  fof(f10,plain,(
% 1.46/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 1.46/0.55    inference(pure_predicate_removal,[],[f2])).
% 1.46/0.55  fof(f2,axiom,(
% 1.46/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r1_tsep_1(X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).
% 1.46/0.55  fof(f64,plain,(
% 1.46/0.55    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))),
% 1.46/0.55    inference(cnf_transformation,[],[f36])).
% 1.46/0.55  fof(f205,plain,(
% 1.46/0.55    spl8_7 | ~spl8_4 | ~spl8_1 | ~spl8_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f200,f104,f100,f112,f202])).
% 1.46/0.55  fof(f200,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f199,f46])).
% 1.46/0.55  fof(f199,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f198,f47])).
% 1.46/0.55  fof(f198,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f197,f48])).
% 1.46/0.55  fof(f197,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f196,f49])).
% 1.46/0.55  fof(f196,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f195,f50])).
% 1.46/0.55  fof(f195,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f194,f51])).
% 1.46/0.55  fof(f194,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f193,f52])).
% 1.46/0.55  fof(f193,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f192,f53])).
% 1.46/0.55  fof(f192,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f191,f54])).
% 1.46/0.55  fof(f191,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f190,f55])).
% 1.46/0.55  fof(f190,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f189,f56])).
% 1.46/0.55  fof(f189,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f188,f57])).
% 1.46/0.55  fof(f188,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f187,f59])).
% 1.46/0.55  fof(f187,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f186,f60])).
% 1.46/0.55  fof(f186,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f185,f61])).
% 1.46/0.55  fof(f185,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f184,f63])).
% 1.46/0.55  fof(f184,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f183,f101])).
% 1.46/0.55  fof(f183,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f179,f105])).
% 1.46/0.55  fof(f179,plain,(
% 1.46/0.55    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.46/0.55    inference(resolution,[],[f64,f96])).
% 1.46/0.55  fof(f96,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(equality_resolution,[],[f71])).
% 1.46/0.55  fof(f71,plain,(
% 1.46/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f38])).
% 1.46/0.55  fof(f178,plain,(
% 1.46/0.55    ~spl8_5 | ~spl8_6 | spl8_3),
% 1.46/0.55    inference(avatar_split_clause,[],[f177,f108,f173,f169])).
% 1.46/0.55  fof(f108,plain,(
% 1.46/0.55    spl8_3 <=> v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.46/0.55  fof(f177,plain,(
% 1.46/0.55    ~sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | ~sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | spl8_3),
% 1.46/0.55    inference(resolution,[],[f110,f77])).
% 1.46/0.55  fof(f77,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f41])).
% 1.46/0.55  fof(f41,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 1.46/0.55    inference(rectify,[],[f40])).
% 1.46/0.55  fof(f40,plain,(
% 1.46/0.55    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 1.46/0.55    inference(flattening,[],[f39])).
% 1.46/0.55  fof(f39,plain,(
% 1.46/0.55    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 1.46/0.55    inference(nnf_transformation,[],[f28])).
% 1.46/0.55  fof(f110,plain,(
% 1.46/0.55    ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | spl8_3),
% 1.46/0.55    inference(avatar_component_clause,[],[f108])).
% 1.46/0.55  fof(f167,plain,(
% 1.46/0.55    spl8_2),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f166])).
% 1.46/0.55  fof(f166,plain,(
% 1.46/0.55    $false | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f165,f46])).
% 1.46/0.55  fof(f165,plain,(
% 1.46/0.55    v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f164,f47])).
% 1.46/0.55  fof(f164,plain,(
% 1.46/0.55    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f163,f48])).
% 1.46/0.55  fof(f163,plain,(
% 1.46/0.55    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f162,f49])).
% 1.46/0.55  fof(f162,plain,(
% 1.46/0.55    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f161,f50])).
% 1.46/0.55  fof(f161,plain,(
% 1.46/0.55    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f160,f51])).
% 1.46/0.55  fof(f160,plain,(
% 1.46/0.55    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f159,f52])).
% 1.46/0.55  fof(f159,plain,(
% 1.46/0.55    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f158,f53])).
% 1.46/0.55  fof(f158,plain,(
% 1.46/0.55    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f157,f54])).
% 1.46/0.55  fof(f157,plain,(
% 1.46/0.55    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f156,f55])).
% 1.46/0.55  fof(f156,plain,(
% 1.46/0.55    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f155,f56])).
% 1.46/0.55  fof(f155,plain,(
% 1.46/0.55    ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f154,f57])).
% 1.46/0.55  fof(f154,plain,(
% 1.46/0.55    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f153,f59])).
% 1.46/0.55  fof(f153,plain,(
% 1.46/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f152,f60])).
% 1.46/0.55  fof(f152,plain,(
% 1.46/0.55    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f151,f61])).
% 1.46/0.55  fof(f151,plain,(
% 1.46/0.55    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(subsumption_resolution,[],[f149,f63])).
% 1.46/0.55  fof(f149,plain,(
% 1.46/0.55    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.46/0.55    inference(resolution,[],[f106,f69])).
% 1.46/0.55  fof(f69,plain,(
% 1.46/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f17])).
% 1.46/0.55  fof(f106,plain,(
% 1.46/0.55    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | spl8_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f104])).
% 1.46/0.55  fof(f148,plain,(
% 1.46/0.55    spl8_1),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f147])).
% 1.46/0.55  fof(f147,plain,(
% 1.46/0.55    $false | spl8_1),
% 1.46/0.55    inference(subsumption_resolution,[],[f146,f46])).
% 1.46/0.55  fof(f146,plain,(
% 1.46/0.55    v2_struct_0(sK2) | spl8_1),
% 1.46/0.55    inference(subsumption_resolution,[],[f145,f47])).
% 1.46/0.55  fof(f145,plain,(
% 1.46/0.55    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.55    inference(subsumption_resolution,[],[f144,f48])).
% 1.46/0.55  fof(f144,plain,(
% 1.46/0.55    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.55    inference(subsumption_resolution,[],[f143,f49])).
% 1.46/0.55  fof(f143,plain,(
% 1.46/0.55    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.55    inference(subsumption_resolution,[],[f142,f50])).
% 1.46/0.56  fof(f142,plain,(
% 1.46/0.56    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f141,f51])).
% 1.46/0.56  fof(f141,plain,(
% 1.46/0.56    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f140,f52])).
% 1.46/0.56  fof(f140,plain,(
% 1.46/0.56    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f139,f53])).
% 1.46/0.56  fof(f139,plain,(
% 1.46/0.56    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f138,f54])).
% 1.46/0.56  fof(f138,plain,(
% 1.46/0.56    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f137,f55])).
% 1.46/0.56  fof(f137,plain,(
% 1.46/0.56    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f136,f56])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f135,f57])).
% 1.46/0.56  fof(f135,plain,(
% 1.46/0.56    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f134,f59])).
% 1.46/0.56  fof(f134,plain,(
% 1.46/0.56    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f133,f60])).
% 1.46/0.56  fof(f133,plain,(
% 1.46/0.56    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f132,f61])).
% 1.46/0.56  fof(f132,plain,(
% 1.46/0.56    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f130,f63])).
% 1.46/0.56  fof(f130,plain,(
% 1.46/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.46/0.56    inference(resolution,[],[f102,f68])).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f17])).
% 1.46/0.56  fof(f102,plain,(
% 1.46/0.56    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f100])).
% 1.46/0.56  fof(f115,plain,(
% 1.46/0.56    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 1.46/0.56    inference(avatar_split_clause,[],[f66,f112,f108,f104,f100])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.46/0.56    inference(cnf_transformation,[],[f36])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (30131)------------------------------
% 1.46/0.56  % (30131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (30131)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (30131)Memory used [KB]: 11129
% 1.46/0.56  % (30131)Time elapsed: 0.106 s
% 1.46/0.56  % (30131)------------------------------
% 1.46/0.56  % (30131)------------------------------
% 1.46/0.56  % (30124)Success in time 0.199 s
%------------------------------------------------------------------------------

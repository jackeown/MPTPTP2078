%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:52 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  221 (1391 expanded)
%              Number of leaves         :   28 ( 699 expanded)
%              Depth                    :   25
%              Number of atoms          : 1607 (34651 expanded)
%              Number of equality atoms :   42 (1566 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f765,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f242,f290,f588,f595,f602,f625,f634,f637,f740,f752,f758,f762])).

fof(f762,plain,
    ( spl10_4
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | spl10_4
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f759,f591])).

fof(f591,plain,
    ( sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl10_12
  <=> sP3(sK5,sK7,sK6,sK4,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f759,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_4 ),
    inference(resolution,[],[f113,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(superposition,[],[f94,f65])).

fof(f65,plain,(
    sK4 = k1_tsep_1(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
      | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)
      | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))
      | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) )
    & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9)
    & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8)
    & sK4 = k1_tsep_1(sK4,sK6,sK7)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v5_pre_topc(sK9,sK7,sK5)
    & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    & v5_pre_topc(sK8,sK6,sK5)
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & v1_borsuk_1(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & v1_borsuk_1(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f9,f31,f30,f29,f28,f27,f26])).

fof(f26,plain,
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK4,X1,X2,X3,X4,X5),sK4,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK4,X1,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X4)
                          & sK4 = k1_tsep_1(sK4,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & v1_borsuk_1(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & v1_borsuk_1(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK4,X1,X2,X3,X4,X5),sK4,X1)
                          | ~ v1_funct_2(k10_tmap_1(sK4,X1,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X4)
                        & sK4 = k1_tsep_1(sK4,X2,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK4)
                & v1_borsuk_1(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & v1_borsuk_1(X2,sK4)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
                        | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),sK4,sK5)
                        | ~ v1_funct_2(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5))
                        | ~ v1_funct_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X4)
                      & sK4 = k1_tsep_1(sK4,X2,X3)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                      & v5_pre_topc(X5,X3,sK5)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5))))
                  & v5_pre_topc(X4,X2,sK5)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK5))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK4)
              & v1_borsuk_1(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & v1_borsuk_1(X2,sK4)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
                      | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),sK4,sK5)
                      | ~ v1_funct_2(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5))
                      | ~ v1_funct_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X4)
                    & sK4 = k1_tsep_1(sK4,X2,X3)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                    & v5_pre_topc(X5,X3,sK5)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5))))
                & v5_pre_topc(X4,X2,sK5)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK5))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK4)
            & v1_borsuk_1(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & v1_borsuk_1(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
                    | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),sK4,sK5)
                    | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5))
                    | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),X3,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),sK6,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X4)
                  & sK4 = k1_tsep_1(sK4,sK6,X3)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                  & v5_pre_topc(X5,X3,sK5)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
              & v5_pre_topc(X4,sK6,sK5)
              & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK4)
          & v1_borsuk_1(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & v1_borsuk_1(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
                  | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),sK4,sK5)
                  | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5))
                  | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)) )
                & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),X3,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),sK6,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X4)
                & sK4 = k1_tsep_1(sK4,sK6,X3)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                & v5_pre_topc(X5,X3,sK5)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
            & v5_pre_topc(X4,sK6,sK5)
            & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK4)
        & v1_borsuk_1(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
                | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),sK4,sK5)
                | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5))
                | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)) )
              & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X4)
              & sK4 = k1_tsep_1(sK4,sK6,sK7)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
              & v5_pre_topc(X5,sK7,sK5)
              & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
          & v5_pre_topc(X4,sK6,sK5)
          & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK7,sK4)
      & v1_borsuk_1(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
              | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),sK4,sK5)
              | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5))
              | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)) )
            & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X5)
            & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X4)
            & sK4 = k1_tsep_1(sK4,sK6,sK7)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
            & v5_pre_topc(X5,sK7,sK5)
            & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
        & v5_pre_topc(X4,sK6,sK5)
        & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
            | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),sK4,sK5)
            | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),u1_struct_0(sK4),u1_struct_0(sK5))
            | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)) )
          & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),X5)
          & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),sK8)
          & sK4 = k1_tsep_1(sK4,sK6,sK7)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
          & v5_pre_topc(X5,sK7,sK5)
          & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5))
          & v1_funct_1(X5) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      & v5_pre_topc(sK8,sK6,sK5)
      & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
          | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),sK4,sK5)
          | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),u1_struct_0(sK4),u1_struct_0(sK5))
          | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)) )
        & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),X5)
        & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),sK8)
        & sK4 = k1_tsep_1(sK4,sK6,sK7)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
        & v5_pre_topc(X5,sK7,sK5)
        & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
        | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)
        | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))
        | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) )
      & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9)
      & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8)
      & sK4 = k1_tsep_1(sK4,sK6,sK7)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      & v5_pre_topc(sK9,sK7,sK5)
      & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP3(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP3(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f113,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_4
  <=> m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f758,plain,
    ( spl10_3
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f754,f346,f107])).

fof(f107,plain,
    ( spl10_3
  <=> v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f346,plain,
    ( spl10_10
  <=> sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f754,plain,
    ( v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)
    | ~ spl10_10 ),
    inference(resolution,[],[f347,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK7,sK6,sK4,X0)
      | v5_pre_topc(X0,sK4,X1) ) ),
    inference(superposition,[],[f81,f65])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f347,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f346])).

fof(f752,plain,
    ( spl10_10
    | ~ spl10_5
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f751,f590,f229,f346])).

fof(f229,plain,
    ( spl10_5
  <=> sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f751,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_5
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f750,f591])).

fof(f750,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f749,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f749,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | v2_struct_0(sK5)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f748,f49])).

fof(f49,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f748,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f741,f50])).

fof(f50,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f741,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5 ),
    inference(resolution,[],[f230,f519])).

fof(f519,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4)
      | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(subsumption_resolution,[],[f518,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f518,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4)
      | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
      | ~ v1_funct_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(subsumption_resolution,[],[f513,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(superposition,[],[f93,f65])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f513,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4)
      | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
      | ~ v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(resolution,[],[f512,f159])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f511,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f511,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f510,f46])).

fof(f46,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f510,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f509,f47])).

fof(f47,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f509,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f508,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f508,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f507,f52])).

fof(f52,plain,(
    v1_borsuk_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f507,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_borsuk_1(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f506,f53])).

fof(f53,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f506,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK6,sK4)
      | ~ v1_borsuk_1(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f505,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f505,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(sK6,sK4)
      | ~ v1_borsuk_1(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f504,f55])).

fof(f55,plain,(
    v1_borsuk_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f504,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_borsuk_1(sK7,sK4)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(sK6,sK4)
      | ~ v1_borsuk_1(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f495,f56])).

fof(f56,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f495,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK7,sK4)
      | ~ v1_borsuk_1(sK7,sK4)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(sK6,sK4)
      | ~ v1_borsuk_1(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(superposition,[],[f85,f65])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ sP1(X1,X3,X4,X2,X0)
      | sP0(X1,X3,X2,X0,X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_borsuk_1(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f20,f19])).

fof(f20,plain,(
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

fof(f12,plain,(
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
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
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

fof(f230,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f229])).

fof(f740,plain,
    ( spl10_5
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f739,f287,f233,f229])).

fof(f233,plain,
    ( spl10_6
  <=> sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f287,plain,
    ( spl10_9
  <=> sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f739,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f738,f57])).

fof(f57,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f738,plain,
    ( ~ v1_funct_1(sK8)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f737,f235])).

fof(f235,plain,
    ( sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f233])).

fof(f737,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f736,f58])).

fof(f58,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f736,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f735,f235])).

fof(f735,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f734,f59])).

fof(f59,plain,(
    v5_pre_topc(sK8,sK6,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f734,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK5)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f733,f235])).

fof(f733,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f732,f60])).

fof(f60,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f732,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f721,f235])).

fof(f721,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f720,f61])).

fof(f61,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f32])).

fof(f720,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f719,f62])).

fof(f62,plain,(
    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f719,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f718,f63])).

fof(f63,plain,(
    v5_pre_topc(sK9,sK7,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f718,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v5_pre_topc(sK9,sK7,sK5)
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f715,f64])).

fof(f64,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f715,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v5_pre_topc(sK9,sK7,sK5)
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(superposition,[],[f574,f289])).

fof(f289,plain,
    ( sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f287])).

fof(f574,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK4,X0,sK4,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(sK4,X0,sK4,sK6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(sK4,X0,sK4,sK7,X1),sK7,X0)
      | ~ v1_funct_2(k3_tmap_1(sK4,X0,sK4,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(sK4,X0,sK4,sK7,X1))
      | sP1(X0,sK7,X1,sK6,sK4)
      | ~ v5_pre_topc(k3_tmap_1(sK4,X0,sK4,sK6,X1),sK6,X0)
      | ~ v1_funct_2(k3_tmap_1(sK4,X0,sK4,sK6,X1),u1_struct_0(sK6),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(sK4,X0,sK4,sK6,X1)) ) ),
    inference(superposition,[],[f78,f65])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f637,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | spl10_11 ),
    inference(subsumption_resolution,[],[f635,f47])).

fof(f635,plain,
    ( ~ l1_pre_topc(sK4)
    | spl10_11 ),
    inference(resolution,[],[f352,f69])).

fof(f69,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f352,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl10_11
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f634,plain,
    ( ~ spl10_11
    | spl10_8
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f633,f590,f283,f350])).

fof(f283,plain,
    ( spl10_8
  <=> sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f633,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl10_8
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f632,f591])).

fof(f632,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f631,f45])).

fof(f631,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f630,f46])).

fof(f630,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f629,f47])).

fof(f629,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f628,f48])).

fof(f628,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f627,f49])).

fof(f627,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f626,f50])).

fof(f626,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f616,f56])).

fof(f616,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(resolution,[],[f307,f285])).

fof(f285,plain,
    ( ~ sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f283])).

fof(f307,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12)
      | ~ m1_pre_topc(X9,X12)
      | ~ m1_pre_topc(sK4,X12)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP3(X8,sK7,sK6,sK4,X11,X10) ) ),
    inference(subsumption_resolution,[],[f306,f92])).

fof(f306,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12)
      | ~ v1_funct_1(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11))
      | ~ m1_pre_topc(X9,X12)
      | ~ m1_pre_topc(sK4,X12)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP3(X8,sK7,sK6,sK4,X11,X10) ) ),
    inference(subsumption_resolution,[],[f293,f157])).

fof(f293,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12)
      | ~ v1_funct_2(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),u1_struct_0(sK4),u1_struct_0(X8))
      | ~ v1_funct_1(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11))
      | ~ m1_pre_topc(X9,X12)
      | ~ m1_pre_topc(sK4,X12)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP3(X8,sK7,sK6,sK4,X11,X10) ) ),
    inference(resolution,[],[f91,f159])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP2(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP2(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f16,f22])).

fof(f22,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP2(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f625,plain,
    ( ~ spl10_11
    | spl10_7
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f624,f590,f239,f350])).

fof(f239,plain,
    ( spl10_7
  <=> sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f624,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl10_7
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f623,f591])).

fof(f623,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f622,f45])).

fof(f622,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f621,f46])).

fof(f621,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f620,f47])).

fof(f620,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f619,f48])).

fof(f619,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f618,f49])).

fof(f618,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f617,f50])).

fof(f617,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f615,f53])).

fof(f615,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(resolution,[],[f307,f241])).

fof(f241,plain,
    ( ~ sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f239])).

fof(f602,plain,(
    spl10_12 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | spl10_12 ),
    inference(subsumption_resolution,[],[f600,f45])).

fof(f600,plain,
    ( v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f599,f46])).

fof(f599,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f598,f47])).

fof(f598,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f597,f53])).

fof(f597,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f596,f56])).

fof(f596,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(resolution,[],[f592,f543])).

fof(f543,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f542,f51])).

fof(f542,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f541,f57])).

fof(f541,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ v1_funct_1(sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f528,f58])).

fof(f528,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f407,f60])).

fof(f407,plain,(
    ! [X66,X67,X65] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f406,f48])).

fof(f406,plain,(
    ! [X66,X67,X65] :
      ( sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f405,f49])).

fof(f405,plain,(
    ! [X66,X67,X65] :
      ( sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f404,f50])).

fof(f404,plain,(
    ! [X66,X67,X65] :
      ( sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f403,f54])).

fof(f403,plain,(
    ! [X66,X67,X65] :
      ( sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f402,f61])).

fof(f402,plain,(
    ! [X66,X67,X65] :
      ( sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f373,f62])).

fof(f373,plain,(
    ! [X66,X67,X65] :
      ( sP3(sK5,sK7,X65,X66,sK9,X67)
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK7,X66)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(resolution,[],[f95,f64])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP3(X1,X3,X2,X0,X5,X4)
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP3(X1,X3,X2,X0,X5,X4)
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
    inference(definition_folding,[],[f18,f24])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f592,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f590])).

fof(f595,plain,
    ( ~ spl10_12
    | spl10_2 ),
    inference(avatar_split_clause,[],[f594,f103,f590])).

fof(f103,plain,
    ( spl10_2
  <=> v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f594,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_2 ),
    inference(resolution,[],[f105,f157])).

fof(f105,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f588,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f586,f45])).

fof(f586,plain,
    ( v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f585,f46])).

fof(f585,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f584,f47])).

fof(f584,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f583,f53])).

fof(f583,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f582,f56])).

fof(f582,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(resolution,[],[f543,f119])).

fof(f119,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_1 ),
    inference(resolution,[],[f92,f101])).

fof(f101,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl10_1
  <=> v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f290,plain,
    ( ~ spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f281,f287,f283])).

fof(f281,plain,
    ( sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    inference(resolution,[],[f222,f116])).

fof(f116,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) ),
    inference(forward_demodulation,[],[f67,f65])).

fof(f67,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) ),
    inference(cnf_transformation,[],[f32])).

fof(f222,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9)
      | sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3)
      | ~ sP2(sK5,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f221,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP2(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f221,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9)
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3))
      | ~ sP2(sK5,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f216,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f216,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9)
      | ~ v1_funct_2(k3_tmap_1(X1,sK5,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3))
      | ~ sP2(sK5,sK7,X3,X2,X1) ) ),
    inference(resolution,[],[f200,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f200,plain,(
    ! [X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      | sK9 = X45
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9)
      | ~ v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f199,f61])).

fof(f199,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9)
      | sK9 = X45
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      | ~ v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f178,f62])).

fof(f178,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9)
      | sK9 = X45
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      | ~ v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(X45) ) ),
    inference(resolution,[],[f86,f64])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f242,plain,
    ( ~ spl10_7
    | spl10_6 ),
    inference(avatar_split_clause,[],[f237,f233,f239])).

fof(f237,plain,
    ( sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    inference(resolution,[],[f209,f115])).

fof(f115,plain,(
    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) ),
    inference(forward_demodulation,[],[f66,f65])).

fof(f66,plain,(
    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f209,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8)
      | sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3)
      | ~ sP2(sK5,sK6,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f208,f88])).

fof(f208,plain,(
    ! [X2,X3,X1] :
      ( sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3)
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8)
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3))
      | ~ sP2(sK5,sK6,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f203,f89])).

fof(f203,plain,(
    ! [X2,X3,X1] :
      ( sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3)
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8)
      | ~ v1_funct_2(k3_tmap_1(X1,sK5,X2,sK6,X3),u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3))
      | ~ sP2(sK5,sK6,X3,X2,X1) ) ),
    inference(resolution,[],[f198,f90])).

fof(f198,plain,(
    ! [X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | sK8 = X44
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8)
      | ~ v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f197,f57])).

fof(f197,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8)
      | sK8 = X44
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f177,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8)
      | sK8 = X44
      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X44) ) ),
    inference(resolution,[],[f86,f60])).

fof(f114,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f68,f111,f107,f103,f99])).

fof(f68,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:56:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (3276)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (3271)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.40/0.56  % (3284)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.40/0.57  % (3283)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.40/0.57  % (3286)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.60/0.57  % (3275)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.60/0.57  % (3267)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.60/0.57  % (3287)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.60/0.57  % (3269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.60/0.58  % (3278)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.60/0.58  % (3265)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.60/0.58  % (3279)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.60/0.58  % (3270)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.60/0.59  % (3288)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.60/0.59  % (3280)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.60/0.60  % (3272)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.60/0.60  % (3277)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.60/0.60  % (3268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.60/0.60  % (3266)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.60/0.61  % (3285)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.61  % (3282)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.60/0.62  % (3290)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.60/0.62  % (3274)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.60/0.63  % (3273)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.60/0.64  % (3281)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.60/0.64  % (3289)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.20/0.66  % (3269)Refutation found. Thanks to Tanya!
% 2.20/0.66  % SZS status Theorem for theBenchmark
% 2.20/0.66  % SZS output start Proof for theBenchmark
% 2.20/0.66  fof(f765,plain,(
% 2.20/0.66    $false),
% 2.20/0.66    inference(avatar_sat_refutation,[],[f114,f242,f290,f588,f595,f602,f625,f634,f637,f740,f752,f758,f762])).
% 2.20/0.66  fof(f762,plain,(
% 2.20/0.66    spl10_4 | ~spl10_12),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f761])).
% 2.20/0.66  fof(f761,plain,(
% 2.20/0.66    $false | (spl10_4 | ~spl10_12)),
% 2.20/0.66    inference(subsumption_resolution,[],[f759,f591])).
% 2.20/0.66  fof(f591,plain,(
% 2.20/0.66    sP3(sK5,sK7,sK6,sK4,sK9,sK8) | ~spl10_12),
% 2.20/0.66    inference(avatar_component_clause,[],[f590])).
% 2.20/0.66  fof(f590,plain,(
% 2.20/0.66    spl10_12 <=> sP3(sK5,sK7,sK6,sK4,sK9,sK8)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 2.20/0.66  fof(f759,plain,(
% 2.20/0.66    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_4),
% 2.20/0.66    inference(resolution,[],[f113,f159])).
% 2.20/0.66  fof(f159,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 2.20/0.66    inference(superposition,[],[f94,f65])).
% 2.20/0.66  fof(f65,plain,(
% 2.20/0.66    sK4 = k1_tsep_1(sK4,sK6,sK7)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f32,plain,(
% 2.20/0.66    ((((((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(sK9,sK7,sK5) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(sK8,sK6,sK5) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & v1_borsuk_1(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & v1_borsuk_1(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.20/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f9,f31,f30,f29,f28,f27,f26])).
% 2.20/0.66  fof(f26,plain,(
% 2.20/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK4,X1,X2,X3,X4,X5),sK4,X1) | ~v1_funct_2(k10_tmap_1(sK4,X1,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_borsuk_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_borsuk_1(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.20/0.66    introduced(choice_axiom,[])).
% 2.20/0.66  fof(f27,plain,(
% 2.20/0.66    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK4,X1,X2,X3,X4,X5),sK4,X1) | ~v1_funct_2(k10_tmap_1(sK4,X1,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_borsuk_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_borsuk_1(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5)))) & v5_pre_topc(X4,X2,sK5) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_borsuk_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_borsuk_1(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 2.20/0.66    introduced(choice_axiom,[])).
% 2.20/0.66  fof(f28,plain,(
% 2.20/0.66    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5)))) & v5_pre_topc(X4,X2,sK5) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_borsuk_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_borsuk_1(X2,sK4) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),X3,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),sK6,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_borsuk_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,sK4) & v1_borsuk_1(sK6,sK4) & ~v2_struct_0(sK6))),
% 2.20/0.66    introduced(choice_axiom,[])).
% 2.20/0.66  fof(f29,plain,(
% 2.20/0.66    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),X3,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),sK6,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_borsuk_1(X3,sK4) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(sK7,sK4) & v1_borsuk_1(sK7,sK4) & ~v2_struct_0(sK7))),
% 2.20/0.66    introduced(choice_axiom,[])).
% 2.20/0.66  fof(f30,plain,(
% 2.20/0.66    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(sK8,sK6,sK5) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK8))),
% 2.20/0.66    introduced(choice_axiom,[])).
% 2.20/0.66  fof(f31,plain,(
% 2.20/0.66    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(sK9,sK7,sK5) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK9))),
% 2.20/0.66    introduced(choice_axiom,[])).
% 2.20/0.66  fof(f9,plain,(
% 2.20/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.66    inference(flattening,[],[f8])).
% 2.20/0.66  fof(f8,plain,(
% 2.20/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.20/0.66    inference(ennf_transformation,[],[f7])).
% 2.20/0.66  fof(f7,negated_conjecture,(
% 2.20/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 2.20/0.66    inference(negated_conjecture,[],[f6])).
% 2.20/0.66  fof(f6,conjecture,(
% 2.20/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).
% 2.20/0.66  fof(f94,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f44])).
% 2.20/0.66  fof(f44,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP3(X0,X1,X2,X3,X4,X5))),
% 2.20/0.66    inference(rectify,[],[f43])).
% 2.20/0.66  fof(f43,plain,(
% 2.20/0.66    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP3(X1,X3,X2,X0,X5,X4))),
% 2.20/0.66    inference(nnf_transformation,[],[f24])).
% 2.20/0.66  fof(f24,plain,(
% 2.20/0.66    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP3(X1,X3,X2,X0,X5,X4))),
% 2.20/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.20/0.66  fof(f113,plain,(
% 2.20/0.66    ~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | spl10_4),
% 2.20/0.66    inference(avatar_component_clause,[],[f111])).
% 2.20/0.66  fof(f111,plain,(
% 2.20/0.66    spl10_4 <=> m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.20/0.66  fof(f758,plain,(
% 2.20/0.66    spl10_3 | ~spl10_10),
% 2.20/0.66    inference(avatar_split_clause,[],[f754,f346,f107])).
% 2.20/0.66  fof(f107,plain,(
% 2.20/0.66    spl10_3 <=> v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.20/0.66  fof(f346,plain,(
% 2.20/0.66    spl10_10 <=> sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 2.20/0.66  fof(f754,plain,(
% 2.20/0.66    v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~spl10_10),
% 2.20/0.66    inference(resolution,[],[f347,f117])).
% 2.20/0.66  fof(f117,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~sP0(X1,sK7,sK6,sK4,X0) | v5_pre_topc(X0,sK4,X1)) )),
% 2.20/0.66    inference(superposition,[],[f81,f65])).
% 2.20/0.66  fof(f81,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f38])).
% 2.20/0.66  fof(f38,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.20/0.66    inference(rectify,[],[f37])).
% 2.20/0.66  fof(f37,plain,(
% 2.20/0.66    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 2.20/0.66    inference(flattening,[],[f36])).
% 2.20/0.66  fof(f36,plain,(
% 2.20/0.66    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 2.20/0.66    inference(nnf_transformation,[],[f19])).
% 2.20/0.66  fof(f19,plain,(
% 2.20/0.66    ! [X1,X3,X2,X0,X4] : (sP0(X1,X3,X2,X0,X4) <=> (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))),
% 2.20/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.20/0.66  fof(f347,plain,(
% 2.20/0.66    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~spl10_10),
% 2.20/0.66    inference(avatar_component_clause,[],[f346])).
% 2.20/0.66  fof(f752,plain,(
% 2.20/0.66    spl10_10 | ~spl10_5 | ~spl10_12),
% 2.20/0.66    inference(avatar_split_clause,[],[f751,f590,f229,f346])).
% 2.20/0.66  fof(f229,plain,(
% 2.20/0.66    spl10_5 <=> sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.20/0.66  fof(f751,plain,(
% 2.20/0.66    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | (~spl10_5 | ~spl10_12)),
% 2.20/0.66    inference(subsumption_resolution,[],[f750,f591])).
% 2.20/0.66  fof(f750,plain,(
% 2.20/0.66    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | ~spl10_5),
% 2.20/0.66    inference(subsumption_resolution,[],[f749,f48])).
% 2.20/0.66  fof(f48,plain,(
% 2.20/0.66    ~v2_struct_0(sK5)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f749,plain,(
% 2.20/0.66    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | v2_struct_0(sK5) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | ~spl10_5),
% 2.20/0.66    inference(subsumption_resolution,[],[f748,f49])).
% 2.20/0.66  fof(f49,plain,(
% 2.20/0.66    v2_pre_topc(sK5)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f748,plain,(
% 2.20/0.66    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | ~spl10_5),
% 2.20/0.66    inference(subsumption_resolution,[],[f741,f50])).
% 2.20/0.66  fof(f50,plain,(
% 2.20/0.66    l1_pre_topc(sK5)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f741,plain,(
% 2.20/0.66    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | ~spl10_5),
% 2.20/0.66    inference(resolution,[],[f230,f519])).
% 2.20/0.66  fof(f519,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4) | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f518,f92])).
% 2.20/0.66  fof(f92,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f44])).
% 2.20/0.66  fof(f518,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4) | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~v1_funct_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f513,f157])).
% 2.20/0.66  fof(f157,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0)) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 2.20/0.66    inference(superposition,[],[f93,f65])).
% 2.20/0.66  fof(f93,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f44])).
% 2.20/0.66  fof(f513,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4) | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 2.20/0.66    inference(resolution,[],[f512,f159])).
% 2.20/0.66  fof(f512,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f511,f45])).
% 2.20/0.66  fof(f45,plain,(
% 2.20/0.66    ~v2_struct_0(sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f511,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f510,f46])).
% 2.20/0.66  fof(f46,plain,(
% 2.20/0.66    v2_pre_topc(sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f510,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f509,f47])).
% 2.20/0.66  fof(f47,plain,(
% 2.20/0.66    l1_pre_topc(sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f509,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f508,f51])).
% 2.20/0.66  fof(f51,plain,(
% 2.20/0.66    ~v2_struct_0(sK6)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f508,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f507,f52])).
% 2.20/0.66  fof(f52,plain,(
% 2.20/0.66    v1_borsuk_1(sK6,sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f507,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~v1_borsuk_1(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f506,f53])).
% 2.20/0.66  fof(f53,plain,(
% 2.20/0.66    m1_pre_topc(sK6,sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f506,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK6,sK4) | ~v1_borsuk_1(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f505,f54])).
% 2.20/0.66  fof(f54,plain,(
% 2.20/0.66    ~v2_struct_0(sK7)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f505,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | ~v1_borsuk_1(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f504,f55])).
% 2.20/0.66  fof(f55,plain,(
% 2.20/0.66    v1_borsuk_1(sK7,sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f504,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~v1_borsuk_1(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | ~v1_borsuk_1(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f495,f56])).
% 2.20/0.66  fof(f56,plain,(
% 2.20/0.66    m1_pre_topc(sK7,sK4)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f495,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK7,sK4) | ~v1_borsuk_1(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | ~v1_borsuk_1(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 2.20/0.66    inference(superposition,[],[f85,f65])).
% 2.20/0.66  fof(f85,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~sP1(X1,X3,X4,X2,X0) | sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f39])).
% 2.20/0.66  fof(f39,plain,(
% 2.20/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((sP0(X1,X3,X2,X0,X4) | ~sP1(X1,X3,X4,X2,X0)) & (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(nnf_transformation,[],[f21])).
% 2.20/0.66  fof(f21,plain,(
% 2.20/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((sP0(X1,X3,X2,X0,X4) <=> sP1(X1,X3,X4,X2,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(definition_folding,[],[f12,f20,f19])).
% 2.20/0.66  fof(f20,plain,(
% 2.20/0.66    ! [X1,X3,X4,X2,X0] : (sP1(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 2.20/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.20/0.66  fof(f12,plain,(
% 2.20/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(flattening,[],[f11])).
% 2.20/0.66  fof(f11,plain,(
% 2.20/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.66    inference(ennf_transformation,[],[f4])).
% 2.20/0.66  fof(f4,axiom,(
% 2.20/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_tmap_1)).
% 2.20/0.66  fof(f230,plain,(
% 2.20/0.66    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~spl10_5),
% 2.20/0.66    inference(avatar_component_clause,[],[f229])).
% 2.20/0.66  fof(f740,plain,(
% 2.20/0.66    spl10_5 | ~spl10_6 | ~spl10_9),
% 2.20/0.66    inference(avatar_split_clause,[],[f739,f287,f233,f229])).
% 2.20/0.66  fof(f233,plain,(
% 2.20/0.66    spl10_6 <=> sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 2.20/0.66  fof(f287,plain,(
% 2.20/0.66    spl10_9 <=> sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.20/0.66  fof(f739,plain,(
% 2.20/0.66    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(subsumption_resolution,[],[f738,f57])).
% 2.20/0.66  fof(f57,plain,(
% 2.20/0.66    v1_funct_1(sK8)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f738,plain,(
% 2.20/0.66    ~v1_funct_1(sK8) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(forward_demodulation,[],[f737,f235])).
% 2.20/0.66  fof(f235,plain,(
% 2.20/0.66    sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~spl10_6),
% 2.20/0.66    inference(avatar_component_clause,[],[f233])).
% 2.20/0.66  fof(f737,plain,(
% 2.20/0.66    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(subsumption_resolution,[],[f736,f58])).
% 2.20/0.66  fof(f58,plain,(
% 2.20/0.66    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f736,plain,(
% 2.20/0.66    ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(forward_demodulation,[],[f735,f235])).
% 2.20/0.66  fof(f735,plain,(
% 2.20/0.66    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(subsumption_resolution,[],[f734,f59])).
% 2.20/0.66  fof(f59,plain,(
% 2.20/0.66    v5_pre_topc(sK8,sK6,sK5)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f734,plain,(
% 2.20/0.66    ~v5_pre_topc(sK8,sK6,sK5) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(forward_demodulation,[],[f733,f235])).
% 2.20/0.66  fof(f733,plain,(
% 2.20/0.66    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(subsumption_resolution,[],[f732,f60])).
% 2.20/0.66  fof(f60,plain,(
% 2.20/0.66    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f732,plain,(
% 2.20/0.66    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 2.20/0.66    inference(forward_demodulation,[],[f721,f235])).
% 2.20/0.66  fof(f721,plain,(
% 2.20/0.66    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 2.20/0.66    inference(subsumption_resolution,[],[f720,f61])).
% 2.20/0.66  fof(f61,plain,(
% 2.20/0.66    v1_funct_1(sK9)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f720,plain,(
% 2.20/0.66    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 2.20/0.66    inference(subsumption_resolution,[],[f719,f62])).
% 2.20/0.66  fof(f62,plain,(
% 2.20/0.66    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f719,plain,(
% 2.20/0.66    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 2.20/0.66    inference(subsumption_resolution,[],[f718,f63])).
% 2.20/0.66  fof(f63,plain,(
% 2.20/0.66    v5_pre_topc(sK9,sK7,sK5)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f718,plain,(
% 2.20/0.66    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v5_pre_topc(sK9,sK7,sK5) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 2.20/0.66    inference(subsumption_resolution,[],[f715,f64])).
% 2.20/0.66  fof(f64,plain,(
% 2.20/0.66    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f715,plain,(
% 2.20/0.66    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v5_pre_topc(sK9,sK7,sK5) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 2.20/0.66    inference(superposition,[],[f574,f289])).
% 2.20/0.66  fof(f289,plain,(
% 2.20/0.66    sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~spl10_9),
% 2.20/0.66    inference(avatar_component_clause,[],[f287])).
% 2.20/0.66  fof(f574,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK4,X0,sK4,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK4,X0,sK4,sK6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(sK4,X0,sK4,sK7,X1),sK7,X0) | ~v1_funct_2(k3_tmap_1(sK4,X0,sK4,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK4,X0,sK4,sK7,X1)) | sP1(X0,sK7,X1,sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,X0,sK4,sK6,X1),sK6,X0) | ~v1_funct_2(k3_tmap_1(sK4,X0,sK4,sK6,X1),u1_struct_0(sK6),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK4,X0,sK4,sK6,X1))) )),
% 2.20/0.66    inference(superposition,[],[f78,f65])).
% 2.20/0.66  fof(f78,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP1(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f35])).
% 2.20/0.66  fof(f35,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP1(X0,X1,X2,X3,X4)))),
% 2.20/0.66    inference(rectify,[],[f34])).
% 2.20/0.66  fof(f34,plain,(
% 2.20/0.66    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 2.20/0.66    inference(flattening,[],[f33])).
% 2.20/0.66  fof(f33,plain,(
% 2.20/0.66    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 2.20/0.66    inference(nnf_transformation,[],[f20])).
% 2.20/0.66  fof(f637,plain,(
% 2.20/0.66    spl10_11),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f636])).
% 2.20/0.66  fof(f636,plain,(
% 2.20/0.66    $false | spl10_11),
% 2.20/0.66    inference(subsumption_resolution,[],[f635,f47])).
% 2.20/0.66  fof(f635,plain,(
% 2.20/0.66    ~l1_pre_topc(sK4) | spl10_11),
% 2.20/0.66    inference(resolution,[],[f352,f69])).
% 2.20/0.66  fof(f69,plain,(
% 2.20/0.66    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f10])).
% 2.20/0.66  fof(f10,plain,(
% 2.20/0.66    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.20/0.66    inference(ennf_transformation,[],[f5])).
% 2.20/0.66  fof(f5,axiom,(
% 2.20/0.66    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.20/0.66  fof(f352,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | spl10_11),
% 2.20/0.66    inference(avatar_component_clause,[],[f350])).
% 2.20/0.66  fof(f350,plain,(
% 2.20/0.66    spl10_11 <=> m1_pre_topc(sK4,sK4)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 2.20/0.66  fof(f634,plain,(
% 2.20/0.66    ~spl10_11 | spl10_8 | ~spl10_12),
% 2.20/0.66    inference(avatar_split_clause,[],[f633,f590,f283,f350])).
% 2.20/0.66  fof(f283,plain,(
% 2.20/0.66    spl10_8 <=> sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 2.20/0.66  fof(f633,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | (spl10_8 | ~spl10_12)),
% 2.20/0.66    inference(subsumption_resolution,[],[f632,f591])).
% 2.20/0.66  fof(f632,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f631,f45])).
% 2.20/0.66  fof(f631,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f630,f46])).
% 2.20/0.66  fof(f630,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f629,f47])).
% 2.20/0.66  fof(f629,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f628,f48])).
% 2.20/0.66  fof(f628,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f627,f49])).
% 2.20/0.66  fof(f627,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f626,f50])).
% 2.20/0.66  fof(f626,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(subsumption_resolution,[],[f616,f56])).
% 2.20/0.66  fof(f616,plain,(
% 2.20/0.66    ~m1_pre_topc(sK7,sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 2.20/0.66    inference(resolution,[],[f307,f285])).
% 2.20/0.66  fof(f285,plain,(
% 2.20/0.66    ~sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) | spl10_8),
% 2.20/0.66    inference(avatar_component_clause,[],[f283])).
% 2.20/0.66  fof(f307,plain,(
% 2.20/0.66    ( ! [X12,X10,X8,X11,X9] : (sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK4,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP3(X8,sK7,sK6,sK4,X11,X10)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f306,f92])).
% 2.20/0.66  fof(f306,plain,(
% 2.20/0.66    ( ! [X12,X10,X8,X11,X9] : (sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12) | ~v1_funct_1(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK4,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP3(X8,sK7,sK6,sK4,X11,X10)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f293,f157])).
% 2.20/0.66  fof(f293,plain,(
% 2.20/0.66    ( ! [X12,X10,X8,X11,X9] : (sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12) | ~v1_funct_2(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),u1_struct_0(sK4),u1_struct_0(X8)) | ~v1_funct_1(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK4,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP3(X8,sK7,sK6,sK4,X11,X10)) )),
% 2.20/0.66    inference(resolution,[],[f91,f159])).
% 2.20/0.66  fof(f91,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP2(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f23])).
% 2.20/0.66  fof(f23,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : (sP2(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(definition_folding,[],[f16,f22])).
% 2.20/0.66  fof(f22,plain,(
% 2.20/0.66    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP2(X1,X3,X4,X2,X0))),
% 2.20/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.20/0.66  fof(f16,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(flattening,[],[f15])).
% 2.20/0.66  fof(f15,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.66    inference(ennf_transformation,[],[f3])).
% 2.20/0.66  fof(f3,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.20/0.66  fof(f625,plain,(
% 2.20/0.66    ~spl10_11 | spl10_7 | ~spl10_12),
% 2.20/0.66    inference(avatar_split_clause,[],[f624,f590,f239,f350])).
% 2.20/0.66  fof(f239,plain,(
% 2.20/0.66    spl10_7 <=> sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 2.20/0.66  fof(f624,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | (spl10_7 | ~spl10_12)),
% 2.20/0.66    inference(subsumption_resolution,[],[f623,f591])).
% 2.20/0.66  fof(f623,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f622,f45])).
% 2.20/0.66  fof(f622,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f621,f46])).
% 2.20/0.66  fof(f621,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f620,f47])).
% 2.20/0.66  fof(f620,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f619,f48])).
% 2.20/0.66  fof(f619,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f618,f49])).
% 2.20/0.66  fof(f618,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f617,f50])).
% 2.20/0.66  fof(f617,plain,(
% 2.20/0.66    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(subsumption_resolution,[],[f615,f53])).
% 2.20/0.66  fof(f615,plain,(
% 2.20/0.66    ~m1_pre_topc(sK6,sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 2.20/0.66    inference(resolution,[],[f307,f241])).
% 2.20/0.66  fof(f241,plain,(
% 2.20/0.66    ~sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) | spl10_7),
% 2.20/0.66    inference(avatar_component_clause,[],[f239])).
% 2.20/0.66  fof(f602,plain,(
% 2.20/0.66    spl10_12),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f601])).
% 2.20/0.66  fof(f601,plain,(
% 2.20/0.66    $false | spl10_12),
% 2.20/0.66    inference(subsumption_resolution,[],[f600,f45])).
% 2.20/0.66  fof(f600,plain,(
% 2.20/0.66    v2_struct_0(sK4) | spl10_12),
% 2.20/0.66    inference(subsumption_resolution,[],[f599,f46])).
% 2.20/0.66  fof(f599,plain,(
% 2.20/0.66    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 2.20/0.66    inference(subsumption_resolution,[],[f598,f47])).
% 2.20/0.66  fof(f598,plain,(
% 2.20/0.66    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 2.20/0.66    inference(subsumption_resolution,[],[f597,f53])).
% 2.20/0.66  fof(f597,plain,(
% 2.20/0.66    ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 2.20/0.66    inference(subsumption_resolution,[],[f596,f56])).
% 2.20/0.66  fof(f596,plain,(
% 2.20/0.66    ~m1_pre_topc(sK7,sK4) | ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 2.20/0.66    inference(resolution,[],[f592,f543])).
% 2.20/0.66  fof(f543,plain,(
% 2.20/0.66    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f542,f51])).
% 2.20/0.66  fof(f542,plain,(
% 2.20/0.66    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK6) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f541,f57])).
% 2.20/0.66  fof(f541,plain,(
% 2.20/0.66    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK6) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f528,f58])).
% 2.20/0.66  fof(f528,plain,(
% 2.20/0.66    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK6) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(resolution,[],[f407,f60])).
% 2.20/0.66  fof(f407,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | sP3(sK5,sK7,X65,X66,sK9,X67) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f406,f48])).
% 2.20/0.66  fof(f406,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f405,f49])).
% 2.20/0.66  fof(f405,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f404,f50])).
% 2.20/0.66  fof(f404,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f403,f54])).
% 2.20/0.66  fof(f403,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | v2_struct_0(sK7) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f402,f61])).
% 2.20/0.66  fof(f402,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~v1_funct_1(sK9) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | v2_struct_0(sK7) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f373,f62])).
% 2.20/0.66  fof(f373,plain,(
% 2.20/0.66    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | v2_struct_0(sK7) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 2.20/0.66    inference(resolution,[],[f95,f64])).
% 2.20/0.66  fof(f95,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP3(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f25])).
% 2.20/0.66  fof(f25,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5] : (sP3(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(definition_folding,[],[f18,f24])).
% 2.20/0.66  fof(f18,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.66    inference(flattening,[],[f17])).
% 2.20/0.66  fof(f17,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.66    inference(ennf_transformation,[],[f2])).
% 2.20/0.66  fof(f2,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.20/0.66  fof(f592,plain,(
% 2.20/0.66    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_12),
% 2.20/0.66    inference(avatar_component_clause,[],[f590])).
% 2.20/0.66  fof(f595,plain,(
% 2.20/0.66    ~spl10_12 | spl10_2),
% 2.20/0.66    inference(avatar_split_clause,[],[f594,f103,f590])).
% 2.20/0.66  fof(f103,plain,(
% 2.20/0.66    spl10_2 <=> v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.20/0.66  fof(f594,plain,(
% 2.20/0.66    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_2),
% 2.20/0.66    inference(resolution,[],[f105,f157])).
% 2.20/0.66  fof(f105,plain,(
% 2.20/0.66    ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | spl10_2),
% 2.20/0.66    inference(avatar_component_clause,[],[f103])).
% 2.20/0.66  fof(f588,plain,(
% 2.20/0.66    spl10_1),
% 2.20/0.66    inference(avatar_contradiction_clause,[],[f587])).
% 2.20/0.66  fof(f587,plain,(
% 2.20/0.66    $false | spl10_1),
% 2.20/0.66    inference(subsumption_resolution,[],[f586,f45])).
% 2.20/0.66  fof(f586,plain,(
% 2.20/0.66    v2_struct_0(sK4) | spl10_1),
% 2.20/0.66    inference(subsumption_resolution,[],[f585,f46])).
% 2.20/0.66  fof(f585,plain,(
% 2.20/0.66    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 2.20/0.66    inference(subsumption_resolution,[],[f584,f47])).
% 2.20/0.66  fof(f584,plain,(
% 2.20/0.66    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 2.20/0.66    inference(subsumption_resolution,[],[f583,f53])).
% 2.20/0.66  fof(f583,plain,(
% 2.20/0.66    ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 2.20/0.66    inference(subsumption_resolution,[],[f582,f56])).
% 2.20/0.66  fof(f582,plain,(
% 2.20/0.66    ~m1_pre_topc(sK7,sK4) | ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 2.20/0.66    inference(resolution,[],[f543,f119])).
% 2.20/0.66  fof(f119,plain,(
% 2.20/0.66    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_1),
% 2.20/0.66    inference(resolution,[],[f92,f101])).
% 2.20/0.66  fof(f101,plain,(
% 2.20/0.66    ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | spl10_1),
% 2.20/0.66    inference(avatar_component_clause,[],[f99])).
% 2.20/0.66  fof(f99,plain,(
% 2.20/0.66    spl10_1 <=> v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 2.20/0.66    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.20/0.66  fof(f290,plain,(
% 2.20/0.66    ~spl10_8 | spl10_9),
% 2.20/0.66    inference(avatar_split_clause,[],[f281,f287,f283])).
% 2.20/0.66  fof(f281,plain,(
% 2.20/0.66    sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 2.20/0.66    inference(resolution,[],[f222,f116])).
% 2.20/0.66  fof(f116,plain,(
% 2.20/0.66    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9)),
% 2.20/0.66    inference(forward_demodulation,[],[f67,f65])).
% 2.20/0.66  fof(f67,plain,(
% 2.20/0.66    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f222,plain,(
% 2.20/0.66    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9) | sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3) | ~sP2(sK5,sK7,X3,X2,X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f221,f88])).
% 2.20/0.66  fof(f88,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP2(X0,X1,X2,X3,X4)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f42])).
% 2.20/0.66  fof(f42,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP2(X0,X1,X2,X3,X4))),
% 2.20/0.66    inference(rectify,[],[f41])).
% 2.20/0.66  fof(f41,plain,(
% 2.20/0.66    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP2(X1,X3,X4,X2,X0))),
% 2.20/0.66    inference(nnf_transformation,[],[f22])).
% 2.20/0.66  fof(f221,plain,(
% 2.20/0.66    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3)) | ~sP2(sK5,sK7,X3,X2,X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f216,f89])).
% 2.20/0.66  fof(f89,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP2(X0,X1,X2,X3,X4)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f42])).
% 2.20/0.66  fof(f216,plain,(
% 2.20/0.66    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9) | ~v1_funct_2(k3_tmap_1(X1,sK5,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3)) | ~sP2(sK5,sK7,X3,X2,X1)) )),
% 2.20/0.66    inference(resolution,[],[f200,f90])).
% 2.20/0.66  fof(f90,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP2(X0,X1,X2,X3,X4)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f42])).
% 2.20/0.66  fof(f200,plain,(
% 2.20/0.66    ( ! [X45] : (~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | sK9 = X45 | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9) | ~v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(X45)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f199,f61])).
% 2.20/0.66  fof(f199,plain,(
% 2.20/0.66    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9) | sK9 = X45 | ~v1_funct_1(sK9) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(X45)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f178,f62])).
% 2.20/0.66  fof(f178,plain,(
% 2.20/0.66    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9) | sK9 = X45 | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(X45)) )),
% 2.20/0.66    inference(resolution,[],[f86,f64])).
% 2.20/0.66  fof(f86,plain,(
% 2.20/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f40])).
% 2.20/0.66  fof(f40,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.20/0.66    inference(nnf_transformation,[],[f14])).
% 2.20/0.66  fof(f14,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.20/0.66    inference(flattening,[],[f13])).
% 2.20/0.66  fof(f13,plain,(
% 2.20/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.20/0.66    inference(ennf_transformation,[],[f1])).
% 2.20/0.66  fof(f1,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.20/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.20/0.66  fof(f242,plain,(
% 2.20/0.66    ~spl10_7 | spl10_6),
% 2.20/0.66    inference(avatar_split_clause,[],[f237,f233,f239])).
% 2.20/0.66  fof(f237,plain,(
% 2.20/0.66    sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 2.20/0.66    inference(resolution,[],[f209,f115])).
% 2.20/0.66  fof(f115,plain,(
% 2.20/0.66    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8)),
% 2.20/0.66    inference(forward_demodulation,[],[f66,f65])).
% 2.20/0.66  fof(f66,plain,(
% 2.20/0.66    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8)),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  fof(f209,plain,(
% 2.20/0.66    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8) | sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3) | ~sP2(sK5,sK6,X3,X2,X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f208,f88])).
% 2.20/0.66  fof(f208,plain,(
% 2.20/0.66    ( ! [X2,X3,X1] : (sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3)) | ~sP2(sK5,sK6,X3,X2,X1)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f203,f89])).
% 2.20/0.66  fof(f203,plain,(
% 2.20/0.66    ( ! [X2,X3,X1] : (sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8) | ~v1_funct_2(k3_tmap_1(X1,sK5,X2,sK6,X3),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3)) | ~sP2(sK5,sK6,X3,X2,X1)) )),
% 2.20/0.66    inference(resolution,[],[f198,f90])).
% 2.20/0.66  fof(f198,plain,(
% 2.20/0.66    ( ! [X44] : (~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sK8 = X44 | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8) | ~v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X44)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f197,f57])).
% 2.20/0.66  fof(f197,plain,(
% 2.20/0.66    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8) | sK8 = X44 | ~v1_funct_1(sK8) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X44)) )),
% 2.20/0.66    inference(subsumption_resolution,[],[f177,f58])).
% 2.20/0.66  fof(f177,plain,(
% 2.20/0.66    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8) | sK8 = X44 | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X44)) )),
% 2.20/0.66    inference(resolution,[],[f86,f60])).
% 2.20/0.66  fof(f114,plain,(
% 2.20/0.66    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 2.20/0.66    inference(avatar_split_clause,[],[f68,f111,f107,f103,f99])).
% 2.20/0.66  fof(f68,plain,(
% 2.20/0.66    ~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 2.20/0.66    inference(cnf_transformation,[],[f32])).
% 2.20/0.66  % SZS output end Proof for theBenchmark
% 2.20/0.66  % (3269)------------------------------
% 2.20/0.66  % (3269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (3269)Termination reason: Refutation
% 2.20/0.66  
% 2.20/0.66  % (3269)Memory used [KB]: 6908
% 2.20/0.66  % (3269)Time elapsed: 0.213 s
% 2.20/0.66  % (3269)------------------------------
% 2.20/0.66  % (3269)------------------------------
% 2.20/0.66  % (3264)Success in time 0.294 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:52 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  235 (1474 expanded)
%              Number of leaves         :   29 ( 738 expanded)
%              Depth                    :   26
%              Number of atoms          : 1704 (36952 expanded)
%              Number of equality atoms :   42 (1669 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f768,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f141,f170,f275,f323,f613,f620,f635,f659,f669,f750,f761,f765])).

fof(f765,plain,
    ( spl11_4
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f762,f616])).

fof(f616,plain,
    ( sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl11_13
  <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f762,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_4 ),
    inference(resolution,[],[f121,f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f102,f70])).

fof(f70,plain,(
    sK5 = k1_tsep_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
      | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
      | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) )
    & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)
    & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)
    & sK5 = k1_tsep_1(sK5,sK7,sK8)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    & v5_pre_topc(sK10,sK8,sK6)
    & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    & v5_pre_topc(sK9,sK7,sK6)
    & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    & v1_funct_1(sK9)
    & m1_pre_topc(sK8,sK5)
    & v1_borsuk_1(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & v1_borsuk_1(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f9,f34,f33,f32,f31,f30,f29])).

fof(f29,plain,
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4)
                          & sK5 = k1_tsep_1(sK5,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK5)
                  & v1_borsuk_1(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & v1_borsuk_1(X2,sK5)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1)
                          | ~ v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4)
                        & sK5 = k1_tsep_1(sK5,X2,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK5)
                & v1_borsuk_1(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
            & v1_borsuk_1(X2,sK5)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                        | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6)
                        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                        | ~ v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4)
                      & sK5 = k1_tsep_1(sK5,X2,X3)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                      & v5_pre_topc(X5,X3,sK6)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                  & v5_pre_topc(X4,X2,sK6)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK5)
              & v1_borsuk_1(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
          & v1_borsuk_1(X2,sK5)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                      | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6)
                      | ~ v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                      | ~ v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4)
                    & sK5 = k1_tsep_1(sK5,X2,X3)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                    & v5_pre_topc(X5,X3,sK6)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                & v5_pre_topc(X4,X2,sK6)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK5)
            & v1_borsuk_1(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & v1_borsuk_1(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                    | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6)
                    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4)
                  & sK5 = k1_tsep_1(sK5,sK7,X3)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                  & v5_pre_topc(X5,X3,sK6)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
              & v5_pre_topc(X4,sK7,sK6)
              & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK5)
          & v1_borsuk_1(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & v1_borsuk_1(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                  | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6)
                  | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                  | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)) )
                & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4)
                & sK5 = k1_tsep_1(sK5,sK7,X3)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                & v5_pre_topc(X5,X3,sK6)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
            & v5_pre_topc(X4,sK7,sK6)
            & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK5)
        & v1_borsuk_1(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6)
                | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)) )
              & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4)
              & sK5 = k1_tsep_1(sK5,sK7,sK8)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
              & v5_pre_topc(X5,sK8,sK6)
              & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
          & v5_pre_topc(X4,sK7,sK6)
          & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK8,sK5)
      & v1_borsuk_1(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
              | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6)
              | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
              | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)) )
            & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5)
            & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4)
            & sK5 = k1_tsep_1(sK5,sK7,sK8)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
            & v5_pre_topc(X5,sK8,sK6)
            & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        & v5_pre_topc(X4,sK7,sK6)
        & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
            | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6)
            | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6))
            | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)) )
          & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5)
          & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9)
          & sK5 = k1_tsep_1(sK5,sK7,sK8)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
          & v5_pre_topc(X5,sK8,sK6)
          & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6))
          & v1_funct_1(X5) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      & v5_pre_topc(sK9,sK7,sK6)
      & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
          | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6)
          | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6))
          | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)) )
        & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5)
        & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9)
        & sK5 = k1_tsep_1(sK5,sK7,sK8)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        & v5_pre_topc(X5,sK8,sK6)
        & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) )
      & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)
      & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)
      & sK5 = k1_tsep_1(sK5,sK7,sK8)
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      & v5_pre_topc(sK10,sK8,sK6)
      & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      & v1_funct_1(sK10) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_tmap_1)).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP4(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP4(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f121,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl11_4
  <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f761,plain,
    ( spl11_3
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f757,f615,f262,f115])).

fof(f115,plain,
    ( spl11_3
  <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f262,plain,
    ( spl11_8
  <=> sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f757,plain,
    ( v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(resolution,[],[f755,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK8,sK7,sK5,X0)
      | v5_pre_topc(X0,sK5,X1) ) ),
    inference(superposition,[],[f85,f70])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f755,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f754,f616])).

fof(f754,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f753,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f753,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f752,f54])).

fof(f54,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f752,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f751,f55])).

fof(f55,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f751,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(resolution,[],[f263,f544])).

fof(f544,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
      | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f543,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f543,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
      | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f538,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f101,f70])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f538,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
      | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(resolution,[],[f537,f192])).

fof(f537,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f536,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f536,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f535,f51])).

fof(f51,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f535,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f534,f52])).

fof(f52,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f534,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f533,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f533,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f532,f57])).

fof(f57,plain,(
    v1_borsuk_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f532,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_borsuk_1(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f531,f58])).

fof(f58,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f531,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK7,sK5)
      | ~ v1_borsuk_1(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f530,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f530,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | ~ v1_borsuk_1(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f529,f60])).

fof(f60,plain,(
    v1_borsuk_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f529,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_borsuk_1(sK8,sK5)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | ~ v1_borsuk_1(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f520,f61])).

fof(f61,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f520,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK8,sK5)
      | ~ v1_borsuk_1(sK8,sK5)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | ~ v1_borsuk_1(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(superposition,[],[f89,f70])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(definition_folding,[],[f11,f21,f20])).

fof(f21,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_tmap_1)).

fof(f263,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f262])).

fof(f750,plain,
    ( spl11_8
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f749,f320,f266,f262])).

fof(f266,plain,
    ( spl11_9
  <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f320,plain,
    ( spl11_12
  <=> sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f749,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f748,f62])).

fof(f62,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f748,plain,
    ( ~ v1_funct_1(sK9)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f747,f268])).

fof(f268,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f266])).

fof(f747,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f746,f63])).

fof(f63,plain,(
    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f35])).

fof(f746,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f745,f268])).

fof(f745,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f744,f64])).

fof(f64,plain,(
    v5_pre_topc(sK9,sK7,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f744,plain,
    ( ~ v5_pre_topc(sK9,sK7,sK6)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f743,f268])).

fof(f743,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f742,f65])).

fof(f65,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f742,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f731,f268])).

fof(f731,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f730,f66])).

fof(f66,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f35])).

fof(f730,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f729,f67])).

fof(f67,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f35])).

fof(f729,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f728,f68])).

fof(f68,plain,(
    v5_pre_topc(sK10,sK8,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f728,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v5_pre_topc(sK10,sK8,sK6)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f725,f69])).

fof(f69,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f725,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v5_pre_topc(sK10,sK8,sK6)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(superposition,[],[f558,f322])).

fof(f322,plain,
    ( sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f320])).

fof(f558,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK8,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK8,X1),sK8,X0)
      | ~ v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK8,X1),u1_struct_0(sK8),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK8,X1))
      | sP1(X0,sK8,X1,sK7,sK5)
      | ~ v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK7,X1),sK7,X0)
      | ~ v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK7,X1)) ) ),
    inference(superposition,[],[f82,f70])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f669,plain,
    ( ~ spl11_7
    | spl11_11
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | ~ spl11_7
    | spl11_11
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f667,f616])).

fof(f667,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f666,f50])).

fof(f666,plain,
    ( v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f665,f51])).

fof(f665,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f664,f52])).

fof(f664,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f663,f53])).

fof(f663,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f662,f54])).

fof(f662,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f661,f55])).

fof(f661,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f660,f140])).

fof(f140,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_7
  <=> m1_pre_topc(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f660,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_11 ),
    inference(subsumption_resolution,[],[f649,f61])).

fof(f649,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_11 ),
    inference(resolution,[],[f340,f318])).

fof(f318,plain,
    ( ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl11_11
  <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f340,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12)
      | ~ m1_pre_topc(X9,X12)
      | ~ m1_pre_topc(sK5,X12)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP4(X8,sK8,sK7,sK5,X11,X10) ) ),
    inference(subsumption_resolution,[],[f339,f100])).

fof(f339,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12)
      | ~ v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11))
      | ~ m1_pre_topc(X9,X12)
      | ~ m1_pre_topc(sK5,X12)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP4(X8,sK8,sK7,sK5,X11,X10) ) ),
    inference(subsumption_resolution,[],[f326,f190])).

fof(f326,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12)
      | ~ v1_funct_2(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),u1_struct_0(sK5),u1_struct_0(X8))
      | ~ v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11))
      | ~ m1_pre_topc(X9,X12)
      | ~ m1_pre_topc(sK5,X12)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP4(X8,sK8,sK7,sK5,X11,X10) ) ),
    inference(resolution,[],[f99,f192])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP3(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP3(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f17,f25])).

fof(f25,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP3(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f659,plain,
    ( ~ spl11_7
    | spl11_10
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | ~ spl11_7
    | spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f657,f616])).

fof(f657,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f656,f50])).

fof(f656,plain,
    ( v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f655,f51])).

fof(f655,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f654,f52])).

fof(f654,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f653,f53])).

fof(f653,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f652,f54])).

fof(f652,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f651,f55])).

fof(f651,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f650,f140])).

fof(f650,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_10 ),
    inference(subsumption_resolution,[],[f648,f58])).

fof(f648,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_10 ),
    inference(resolution,[],[f340,f274])).

fof(f274,plain,
    ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl11_10
  <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f635,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | spl11_13 ),
    inference(subsumption_resolution,[],[f633,f50])).

fof(f633,plain,
    ( v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f632,f51])).

fof(f632,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f631,f52])).

fof(f631,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f630,f58])).

fof(f630,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f629,f61])).

fof(f629,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(resolution,[],[f617,f581])).

fof(f581,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f580,f56])).

fof(f580,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f579,f62])).

fof(f579,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ v1_funct_1(sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f566,f63])).

fof(f566,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f432,f65])).

fof(f432,plain,(
    ! [X66,X67,X65] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f431,f53])).

fof(f431,plain,(
    ! [X66,X67,X65] :
      ( sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f430,f54])).

fof(f430,plain,(
    ! [X66,X67,X65] :
      ( sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f429,f55])).

fof(f429,plain,(
    ! [X66,X67,X65] :
      ( sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f428,f59])).

fof(f428,plain,(
    ! [X66,X67,X65] :
      ( sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f427,f66])).

fof(f427,plain,(
    ! [X66,X67,X65] :
      ( sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(subsumption_resolution,[],[f398,f67])).

fof(f398,plain,(
    ! [X66,X67,X65] :
      ( sP4(sK6,sK8,X65,X66,sK10,X67)
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6))))
      | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6))
      | ~ v1_funct_1(X67)
      | ~ m1_pre_topc(sK8,X66)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(X65,X66)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X66)
      | ~ v2_pre_topc(X66)
      | v2_struct_0(X66) ) ),
    inference(resolution,[],[f103,f69])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP4(X1,X3,X2,X0,X5,X4)
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP4(X1,X3,X2,X0,X5,X4)
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
    inference(definition_folding,[],[f19,f27])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f617,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f615])).

fof(f620,plain,
    ( ~ spl11_13
    | spl11_2 ),
    inference(avatar_split_clause,[],[f619,f111,f615])).

fof(f111,plain,
    ( spl11_2
  <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f619,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_2 ),
    inference(resolution,[],[f113,f190])).

fof(f113,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f613,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f611,f50])).

fof(f611,plain,
    ( v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f610,f51])).

fof(f610,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f609,f52])).

fof(f609,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f608,f58])).

fof(f608,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f607,f61])).

fof(f607,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(resolution,[],[f581,f144])).

fof(f144,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_1 ),
    inference(resolution,[],[f100,f109])).

fof(f109,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl11_1
  <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f323,plain,
    ( ~ spl11_11
    | spl11_12 ),
    inference(avatar_split_clause,[],[f314,f320,f316])).

fof(f314,plain,
    ( sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    inference(resolution,[],[f255,f124])).

fof(f124,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(forward_demodulation,[],[f72,f70])).

fof(f72,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(cnf_transformation,[],[f35])).

fof(f255,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f254,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP3(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f254,plain,(
    ! [X2,X3,X1] :
      ( sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3))
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f249,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f249,plain,(
    ! [X2,X3,X1] :
      ( sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | ~ v1_funct_2(k3_tmap_1(X1,sK6,X2,sK8,X3),u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3))
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(resolution,[],[f233,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f233,plain,(
    ! [X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | sK10 = X45
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f232,f66])).

fof(f232,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | sK10 = X45
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f211,f67])).

fof(f211,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | sK10 = X45
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(resolution,[],[f94,f69])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

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

fof(f275,plain,
    ( ~ spl11_10
    | spl11_9 ),
    inference(avatar_split_clause,[],[f270,f266,f272])).

fof(f270,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    inference(resolution,[],[f242,f123])).

fof(f123,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(forward_demodulation,[],[f71,f70])).

fof(f71,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f242,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f241,f96])).

fof(f241,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3))
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f236,f97])).

fof(f236,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | ~ v1_funct_2(k3_tmap_1(X1,sK6,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3))
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(resolution,[],[f231,f98])).

fof(f231,plain,(
    ! [X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | sK9 = X44
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f230,f62])).

fof(f230,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | sK9 = X44
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f210,f63])).

fof(f210,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | sK9 = X44
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(resolution,[],[f94,f65])).

fof(f170,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl11_5 ),
    inference(subsumption_resolution,[],[f168,f50])).

fof(f168,plain,
    ( v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f167,f52])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f166,f56])).

fof(f166,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f165,f58])).

fof(f165,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f164,f59])).

fof(f164,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f163,f61])).

fof(f163,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(resolution,[],[f93,f130])).

fof(f130,plain,
    ( ~ sP2(sK5,sK8,sK7)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl11_5
  <=> sP2(sK5,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f141,plain,
    ( ~ spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f136,f138,f128])).

fof(f136,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ sP2(sK5,sK8,sK7) ),
    inference(superposition,[],[f92,f70])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f122,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f73,f119,f115,f111,f107])).

fof(f73,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (5145)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (5143)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (5151)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (5134)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (5136)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.24/0.51  % (5137)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.24/0.52  % (5141)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.24/0.52  % (5133)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.52  % (5132)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.24/0.52  % (5154)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.24/0.52  % (5146)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.24/0.52  % (5144)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.24/0.52  % (5148)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.24/0.53  % (5135)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.24/0.53  % (5152)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.34/0.53  % (5138)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.34/0.53  % (5150)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.34/0.54  % (5156)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.34/0.54  % (5142)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.34/0.54  % (5140)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.34/0.54  % (5155)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.34/0.54  % (5157)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.34/0.54  % (5149)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.34/0.55  % (5147)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.34/0.55  % (5153)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.34/0.55  % (5139)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.34/0.56  % (5136)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f768,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(avatar_sat_refutation,[],[f122,f141,f170,f275,f323,f613,f620,f635,f659,f669,f750,f761,f765])).
% 1.34/0.56  fof(f765,plain,(
% 1.34/0.56    spl11_4 | ~spl11_13),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f764])).
% 1.34/0.56  fof(f764,plain,(
% 1.34/0.56    $false | (spl11_4 | ~spl11_13)),
% 1.34/0.56    inference(subsumption_resolution,[],[f762,f616])).
% 1.34/0.56  fof(f616,plain,(
% 1.34/0.56    sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_13),
% 1.34/0.56    inference(avatar_component_clause,[],[f615])).
% 1.34/0.56  fof(f615,plain,(
% 1.34/0.56    spl11_13 <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.34/0.56  fof(f762,plain,(
% 1.34/0.56    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_4),
% 1.34/0.56    inference(resolution,[],[f121,f192])).
% 1.34/0.56  fof(f192,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.34/0.56    inference(superposition,[],[f102,f70])).
% 1.34/0.56  fof(f70,plain,(
% 1.34/0.56    sK5 = k1_tsep_1(sK5,sK7,sK8)),
% 1.34/0.56    inference(cnf_transformation,[],[f35])).
% 1.34/0.56  fof(f35,plain,(
% 1.34/0.56    ((((((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(sK10,sK8,sK6) & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(sK9,sK7,sK6) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(sK9)) & m1_pre_topc(sK8,sK5) & v1_borsuk_1(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & v1_borsuk_1(sK7,sK5) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f9,f34,f33,f32,f31,f30,f29])).
% 1.34/0.56  fof(f29,plain,(
% 1.34/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1) | ~v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_borsuk_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_borsuk_1(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f30,plain,(
% 1.34/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1) | ~v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_borsuk_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_borsuk_1(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6)))) & v5_pre_topc(X4,X2,sK6) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_borsuk_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_borsuk_1(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f31,plain,(
% 1.34/0.56    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6)))) & v5_pre_topc(X4,X2,sK6) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_borsuk_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_borsuk_1(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_borsuk_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & v1_borsuk_1(sK7,sK5) & ~v2_struct_0(sK7))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f32,plain,(
% 1.34/0.56    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_borsuk_1(X3,sK5) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(sK8,sK5) & v1_borsuk_1(sK8,sK5) & ~v2_struct_0(sK8))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f33,plain,(
% 1.34/0.56    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(sK9,sK7,sK6) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(sK9))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f34,plain,(
% 1.34/0.56    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(sK10,sK8,sK6) & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(sK10))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f9,plain,(
% 1.34/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.34/0.56    inference(flattening,[],[f8])).
% 1.34/0.56  fof(f8,plain,(
% 1.34/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.34/0.56    inference(ennf_transformation,[],[f7])).
% 1.34/0.56  fof(f7,negated_conjecture,(
% 1.34/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.34/0.56    inference(negated_conjecture,[],[f6])).
% 1.34/0.56  fof(f6,conjecture,(
% 1.34/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.34/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_tmap_1)).
% 1.34/0.56  fof(f102,plain,(
% 1.34/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f49])).
% 1.34/0.56  fof(f49,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP4(X0,X1,X2,X3,X4,X5))),
% 1.34/0.56    inference(rectify,[],[f48])).
% 1.34/0.57  fof(f48,plain,(
% 1.34/0.57    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP4(X1,X3,X2,X0,X5,X4))),
% 1.34/0.57    inference(nnf_transformation,[],[f27])).
% 1.34/0.57  fof(f27,plain,(
% 1.34/0.57    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP4(X1,X3,X2,X0,X5,X4))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.34/0.57  fof(f121,plain,(
% 1.34/0.57    ~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | spl11_4),
% 1.34/0.57    inference(avatar_component_clause,[],[f119])).
% 1.34/0.57  fof(f119,plain,(
% 1.34/0.57    spl11_4 <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.34/0.57  fof(f761,plain,(
% 1.34/0.57    spl11_3 | ~spl11_8 | ~spl11_13),
% 1.34/0.57    inference(avatar_split_clause,[],[f757,f615,f262,f115])).
% 1.34/0.57  fof(f115,plain,(
% 1.34/0.57    spl11_3 <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.34/0.57  fof(f262,plain,(
% 1.34/0.57    spl11_8 <=> sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.34/0.57  fof(f757,plain,(
% 1.34/0.57    v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | (~spl11_8 | ~spl11_13)),
% 1.34/0.57    inference(resolution,[],[f755,f142])).
% 1.34/0.57  fof(f142,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~sP0(X1,sK8,sK7,sK5,X0) | v5_pre_topc(X0,sK5,X1)) )),
% 1.34/0.57    inference(superposition,[],[f85,f70])).
% 1.34/0.57  fof(f85,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f41])).
% 1.34/0.57  fof(f41,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.34/0.57    inference(rectify,[],[f40])).
% 1.34/0.57  fof(f40,plain,(
% 1.34/0.57    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.34/0.57    inference(flattening,[],[f39])).
% 1.34/0.57  fof(f39,plain,(
% 1.34/0.57    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.34/0.57    inference(nnf_transformation,[],[f20])).
% 1.34/0.57  fof(f20,plain,(
% 1.34/0.57    ! [X1,X3,X2,X0,X4] : (sP0(X1,X3,X2,X0,X4) <=> (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.57  fof(f755,plain,(
% 1.34/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | (~spl11_8 | ~spl11_13)),
% 1.34/0.57    inference(subsumption_resolution,[],[f754,f616])).
% 1.34/0.57  fof(f754,plain,(
% 1.34/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.34/0.57    inference(subsumption_resolution,[],[f753,f53])).
% 1.34/0.57  fof(f53,plain,(
% 1.34/0.57    ~v2_struct_0(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f753,plain,(
% 1.34/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.34/0.57    inference(subsumption_resolution,[],[f752,f54])).
% 1.34/0.57  fof(f54,plain,(
% 1.34/0.57    v2_pre_topc(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f752,plain,(
% 1.34/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.34/0.57    inference(subsumption_resolution,[],[f751,f55])).
% 1.34/0.57  fof(f55,plain,(
% 1.34/0.57    l1_pre_topc(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f751,plain,(
% 1.34/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.34/0.57    inference(resolution,[],[f263,f544])).
% 1.34/0.57  fof(f544,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f543,f100])).
% 1.34/0.57  fof(f100,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f49])).
% 1.34/0.57  fof(f543,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f538,f190])).
% 1.34/0.57  fof(f190,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.34/0.57    inference(superposition,[],[f101,f70])).
% 1.34/0.57  fof(f101,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f49])).
% 1.34/0.57  fof(f538,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.34/0.57    inference(resolution,[],[f537,f192])).
% 1.34/0.57  fof(f537,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f536,f50])).
% 1.34/0.57  fof(f50,plain,(
% 1.34/0.57    ~v2_struct_0(sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f536,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f535,f51])).
% 1.34/0.57  fof(f51,plain,(
% 1.34/0.57    v2_pre_topc(sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f535,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f534,f52])).
% 1.34/0.57  fof(f52,plain,(
% 1.34/0.57    l1_pre_topc(sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f534,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f533,f56])).
% 1.34/0.57  fof(f56,plain,(
% 1.34/0.57    ~v2_struct_0(sK7)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f533,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f532,f57])).
% 1.34/0.57  fof(f57,plain,(
% 1.34/0.57    v1_borsuk_1(sK7,sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f532,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~v1_borsuk_1(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f531,f58])).
% 1.34/0.57  fof(f58,plain,(
% 1.34/0.57    m1_pre_topc(sK7,sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f531,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK7,sK5) | ~v1_borsuk_1(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f530,f59])).
% 1.34/0.57  fof(f59,plain,(
% 1.34/0.57    ~v2_struct_0(sK8)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f530,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | ~v1_borsuk_1(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f529,f60])).
% 1.34/0.57  fof(f60,plain,(
% 1.34/0.57    v1_borsuk_1(sK8,sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f529,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~v1_borsuk_1(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | ~v1_borsuk_1(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f520,f61])).
% 1.34/0.57  fof(f61,plain,(
% 1.34/0.57    m1_pre_topc(sK8,sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f520,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK8,sK5) | ~v1_borsuk_1(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | ~v1_borsuk_1(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.34/0.57    inference(superposition,[],[f89,f70])).
% 1.34/0.57  fof(f89,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~sP1(X1,X3,X4,X2,X0) | sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f42])).
% 1.34/0.57  fof(f42,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((sP0(X1,X3,X2,X0,X4) | ~sP1(X1,X3,X4,X2,X0)) & (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(nnf_transformation,[],[f22])).
% 1.34/0.57  fof(f22,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((sP0(X1,X3,X2,X0,X4) <=> sP1(X1,X3,X4,X2,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(definition_folding,[],[f11,f21,f20])).
% 1.34/0.57  fof(f21,plain,(
% 1.34/0.57    ! [X1,X3,X4,X2,X0] : (sP1(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.34/0.57  fof(f11,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(flattening,[],[f10])).
% 1.34/0.57  fof(f10,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f5])).
% 1.34/0.57  fof(f5,axiom,(
% 1.34/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 1.34/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_tmap_1)).
% 1.34/0.57  fof(f263,plain,(
% 1.34/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~spl11_8),
% 1.34/0.57    inference(avatar_component_clause,[],[f262])).
% 1.34/0.57  fof(f750,plain,(
% 1.34/0.57    spl11_8 | ~spl11_9 | ~spl11_12),
% 1.34/0.57    inference(avatar_split_clause,[],[f749,f320,f266,f262])).
% 1.34/0.57  fof(f266,plain,(
% 1.34/0.57    spl11_9 <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.34/0.57  fof(f320,plain,(
% 1.34/0.57    spl11_12 <=> sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.34/0.57  fof(f749,plain,(
% 1.34/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(subsumption_resolution,[],[f748,f62])).
% 1.34/0.57  fof(f62,plain,(
% 1.34/0.57    v1_funct_1(sK9)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f748,plain,(
% 1.34/0.57    ~v1_funct_1(sK9) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f747,f268])).
% 1.34/0.57  fof(f268,plain,(
% 1.34/0.57    sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~spl11_9),
% 1.34/0.57    inference(avatar_component_clause,[],[f266])).
% 1.34/0.57  fof(f747,plain,(
% 1.34/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(subsumption_resolution,[],[f746,f63])).
% 1.34/0.57  fof(f63,plain,(
% 1.34/0.57    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f746,plain,(
% 1.34/0.57    ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f745,f268])).
% 1.34/0.57  fof(f745,plain,(
% 1.34/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(subsumption_resolution,[],[f744,f64])).
% 1.34/0.57  fof(f64,plain,(
% 1.34/0.57    v5_pre_topc(sK9,sK7,sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f744,plain,(
% 1.34/0.57    ~v5_pre_topc(sK9,sK7,sK6) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f743,f268])).
% 1.34/0.57  fof(f743,plain,(
% 1.34/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(subsumption_resolution,[],[f742,f65])).
% 1.34/0.57  fof(f65,plain,(
% 1.34/0.57    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f742,plain,(
% 1.34/0.57    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f731,f268])).
% 1.34/0.57  fof(f731,plain,(
% 1.34/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f730,f66])).
% 1.34/0.57  fof(f66,plain,(
% 1.34/0.57    v1_funct_1(sK10)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f730,plain,(
% 1.34/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f729,f67])).
% 1.34/0.57  fof(f67,plain,(
% 1.34/0.57    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f729,plain,(
% 1.34/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f728,f68])).
% 1.34/0.57  fof(f68,plain,(
% 1.34/0.57    v5_pre_topc(sK10,sK8,sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f728,plain,(
% 1.34/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v5_pre_topc(sK10,sK8,sK6) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f725,f69])).
% 1.34/0.57  fof(f69,plain,(
% 1.34/0.57    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f725,plain,(
% 1.34/0.57    ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v5_pre_topc(sK10,sK8,sK6) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.34/0.57    inference(superposition,[],[f558,f322])).
% 1.34/0.57  fof(f322,plain,(
% 1.34/0.57    sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~spl11_12),
% 1.34/0.57    inference(avatar_component_clause,[],[f320])).
% 1.34/0.57  fof(f558,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK8,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK8,X1),sK8,X0) | ~v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK8,X1),u1_struct_0(sK8),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK8,X1)) | sP1(X0,sK8,X1,sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK7,X1),sK7,X0) | ~v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK7,X1))) )),
% 1.34/0.57    inference(superposition,[],[f82,f70])).
% 1.34/0.57  fof(f82,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP1(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f38,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.34/0.57    inference(rectify,[],[f37])).
% 1.34/0.57  fof(f37,plain,(
% 1.34/0.57    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.34/0.57    inference(flattening,[],[f36])).
% 1.34/0.57  fof(f36,plain,(
% 1.34/0.57    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.34/0.57    inference(nnf_transformation,[],[f21])).
% 1.34/0.57  fof(f669,plain,(
% 1.34/0.57    ~spl11_7 | spl11_11 | ~spl11_13),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f668])).
% 1.34/0.57  fof(f668,plain,(
% 1.34/0.57    $false | (~spl11_7 | spl11_11 | ~spl11_13)),
% 1.34/0.57    inference(subsumption_resolution,[],[f667,f616])).
% 1.34/0.57  fof(f667,plain,(
% 1.34/0.57    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f666,f50])).
% 1.34/0.57  fof(f666,plain,(
% 1.34/0.57    v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f665,f51])).
% 1.34/0.57  fof(f665,plain,(
% 1.34/0.57    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f664,f52])).
% 1.34/0.57  fof(f664,plain,(
% 1.34/0.57    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f663,f53])).
% 1.34/0.57  fof(f663,plain,(
% 1.34/0.57    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f662,f54])).
% 1.34/0.57  fof(f662,plain,(
% 1.34/0.57    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f661,f55])).
% 1.34/0.57  fof(f661,plain,(
% 1.34/0.57    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.34/0.57    inference(subsumption_resolution,[],[f660,f140])).
% 1.34/0.57  fof(f140,plain,(
% 1.34/0.57    m1_pre_topc(sK5,sK5) | ~spl11_7),
% 1.34/0.57    inference(avatar_component_clause,[],[f138])).
% 1.34/0.57  fof(f138,plain,(
% 1.34/0.57    spl11_7 <=> m1_pre_topc(sK5,sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.34/0.57  fof(f660,plain,(
% 1.34/0.57    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_11),
% 1.34/0.57    inference(subsumption_resolution,[],[f649,f61])).
% 1.34/0.57  fof(f649,plain,(
% 1.34/0.57    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_11),
% 1.34/0.57    inference(resolution,[],[f340,f318])).
% 1.34/0.57  fof(f318,plain,(
% 1.34/0.57    ~sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) | spl11_11),
% 1.34/0.57    inference(avatar_component_clause,[],[f316])).
% 1.34/0.57  fof(f316,plain,(
% 1.34/0.57    spl11_11 <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.34/0.57  fof(f340,plain,(
% 1.34/0.57    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f339,f100])).
% 1.34/0.57  fof(f339,plain,(
% 1.34/0.57    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f326,f190])).
% 1.34/0.57  fof(f326,plain,(
% 1.34/0.57    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~v1_funct_2(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),u1_struct_0(sK5),u1_struct_0(X8)) | ~v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.34/0.57    inference(resolution,[],[f99,f192])).
% 1.34/0.57  fof(f99,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP3(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f26])).
% 1.34/0.57  fof(f26,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : (sP3(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(definition_folding,[],[f17,f25])).
% 1.34/0.57  fof(f25,plain,(
% 1.34/0.57    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP3(X1,X3,X4,X2,X0))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.34/0.57  fof(f17,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(flattening,[],[f16])).
% 1.34/0.57  fof(f16,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f4])).
% 1.34/0.57  fof(f4,axiom,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.34/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.34/0.57  fof(f659,plain,(
% 1.34/0.57    ~spl11_7 | spl11_10 | ~spl11_13),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f658])).
% 1.34/0.57  fof(f658,plain,(
% 1.34/0.57    $false | (~spl11_7 | spl11_10 | ~spl11_13)),
% 1.34/0.57    inference(subsumption_resolution,[],[f657,f616])).
% 1.34/0.57  fof(f657,plain,(
% 1.34/0.57    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f656,f50])).
% 1.34/0.57  fof(f656,plain,(
% 1.34/0.57    v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f655,f51])).
% 1.34/0.57  fof(f655,plain,(
% 1.34/0.57    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f654,f52])).
% 1.34/0.57  fof(f654,plain,(
% 1.34/0.57    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f653,f53])).
% 1.34/0.57  fof(f653,plain,(
% 1.34/0.57    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f652,f54])).
% 1.34/0.57  fof(f652,plain,(
% 1.34/0.57    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f651,f55])).
% 1.34/0.57  fof(f651,plain,(
% 1.34/0.57    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.34/0.57    inference(subsumption_resolution,[],[f650,f140])).
% 1.34/0.57  fof(f650,plain,(
% 1.34/0.57    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_10),
% 1.34/0.57    inference(subsumption_resolution,[],[f648,f58])).
% 1.34/0.57  fof(f648,plain,(
% 1.34/0.57    ~m1_pre_topc(sK7,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_10),
% 1.34/0.57    inference(resolution,[],[f340,f274])).
% 1.34/0.57  fof(f274,plain,(
% 1.34/0.57    ~sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) | spl11_10),
% 1.34/0.57    inference(avatar_component_clause,[],[f272])).
% 1.34/0.57  fof(f272,plain,(
% 1.34/0.57    spl11_10 <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.34/0.57  fof(f635,plain,(
% 1.34/0.57    spl11_13),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f634])).
% 1.34/0.57  fof(f634,plain,(
% 1.34/0.57    $false | spl11_13),
% 1.34/0.57    inference(subsumption_resolution,[],[f633,f50])).
% 1.34/0.57  fof(f633,plain,(
% 1.34/0.57    v2_struct_0(sK5) | spl11_13),
% 1.34/0.57    inference(subsumption_resolution,[],[f632,f51])).
% 1.34/0.57  fof(f632,plain,(
% 1.34/0.57    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.34/0.57    inference(subsumption_resolution,[],[f631,f52])).
% 1.34/0.57  fof(f631,plain,(
% 1.34/0.57    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.34/0.57    inference(subsumption_resolution,[],[f630,f58])).
% 1.34/0.57  fof(f630,plain,(
% 1.34/0.57    ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.34/0.57    inference(subsumption_resolution,[],[f629,f61])).
% 1.34/0.57  fof(f629,plain,(
% 1.34/0.57    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.34/0.57    inference(resolution,[],[f617,f581])).
% 1.34/0.57  fof(f581,plain,(
% 1.34/0.57    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f580,f56])).
% 1.34/0.57  fof(f580,plain,(
% 1.34/0.57    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f579,f62])).
% 1.34/0.57  fof(f579,plain,(
% 1.34/0.57    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~v1_funct_1(sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f566,f63])).
% 1.34/0.57  fof(f566,plain,(
% 1.34/0.57    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(resolution,[],[f432,f65])).
% 1.34/0.57  fof(f432,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f431,f53])).
% 1.34/0.57  fof(f431,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f430,f54])).
% 1.34/0.57  fof(f430,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f429,f55])).
% 1.34/0.57  fof(f429,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f428,f59])).
% 1.34/0.57  fof(f428,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f427,f66])).
% 1.34/0.57  fof(f427,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_1(sK10) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f398,f67])).
% 1.34/0.57  fof(f398,plain,(
% 1.34/0.57    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.34/0.57    inference(resolution,[],[f103,f69])).
% 1.34/0.57  fof(f103,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP4(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f28])).
% 1.34/0.57  fof(f28,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : (sP4(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(definition_folding,[],[f19,f27])).
% 1.34/0.57  fof(f19,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(flattening,[],[f18])).
% 1.34/0.57  fof(f18,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f2])).
% 1.34/0.57  fof(f2,axiom,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.34/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.34/0.57  fof(f617,plain,(
% 1.34/0.57    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_13),
% 1.34/0.57    inference(avatar_component_clause,[],[f615])).
% 1.34/0.57  fof(f620,plain,(
% 1.34/0.57    ~spl11_13 | spl11_2),
% 1.34/0.57    inference(avatar_split_clause,[],[f619,f111,f615])).
% 1.34/0.57  fof(f111,plain,(
% 1.34/0.57    spl11_2 <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.34/0.57  fof(f619,plain,(
% 1.34/0.57    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_2),
% 1.34/0.57    inference(resolution,[],[f113,f190])).
% 1.34/0.57  fof(f113,plain,(
% 1.34/0.57    ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | spl11_2),
% 1.34/0.57    inference(avatar_component_clause,[],[f111])).
% 1.34/0.57  fof(f613,plain,(
% 1.34/0.57    spl11_1),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f612])).
% 1.34/0.57  fof(f612,plain,(
% 1.34/0.57    $false | spl11_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f611,f50])).
% 1.34/0.57  fof(f611,plain,(
% 1.34/0.57    v2_struct_0(sK5) | spl11_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f610,f51])).
% 1.34/0.57  fof(f610,plain,(
% 1.34/0.57    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f609,f52])).
% 1.34/0.57  fof(f609,plain,(
% 1.34/0.57    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f608,f58])).
% 1.34/0.57  fof(f608,plain,(
% 1.34/0.57    ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f607,f61])).
% 1.34/0.57  fof(f607,plain,(
% 1.34/0.57    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.34/0.57    inference(resolution,[],[f581,f144])).
% 1.34/0.57  fof(f144,plain,(
% 1.34/0.57    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_1),
% 1.34/0.57    inference(resolution,[],[f100,f109])).
% 1.34/0.57  fof(f109,plain,(
% 1.34/0.57    ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | spl11_1),
% 1.34/0.57    inference(avatar_component_clause,[],[f107])).
% 1.34/0.57  fof(f107,plain,(
% 1.34/0.57    spl11_1 <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.34/0.57  fof(f323,plain,(
% 1.34/0.57    ~spl11_11 | spl11_12),
% 1.34/0.57    inference(avatar_split_clause,[],[f314,f320,f316])).
% 1.34/0.57  fof(f314,plain,(
% 1.34/0.57    sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.34/0.57    inference(resolution,[],[f255,f124])).
% 1.34/0.57  fof(f124,plain,(
% 1.34/0.57    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)),
% 1.34/0.57    inference(forward_demodulation,[],[f72,f70])).
% 1.34/0.57  fof(f72,plain,(
% 1.34/0.57    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f255,plain,(
% 1.34/0.57    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f254,f96])).
% 1.34/0.57  fof(f96,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f47])).
% 1.34/0.57  fof(f47,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP3(X0,X1,X2,X3,X4))),
% 1.34/0.57    inference(rectify,[],[f46])).
% 1.34/0.57  fof(f46,plain,(
% 1.34/0.57    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP3(X1,X3,X4,X2,X0))),
% 1.34/0.57    inference(nnf_transformation,[],[f25])).
% 1.34/0.57  fof(f254,plain,(
% 1.34/0.57    ( ! [X2,X3,X1] : (sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3)) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f249,f97])).
% 1.34/0.57  fof(f97,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f47])).
% 1.34/0.57  fof(f249,plain,(
% 1.34/0.57    ( ! [X2,X3,X1] : (sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | ~v1_funct_2(k3_tmap_1(X1,sK6,X2,sK8,X3),u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3)) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.34/0.57    inference(resolution,[],[f233,f98])).
% 1.34/0.57  fof(f98,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f47])).
% 1.34/0.57  fof(f233,plain,(
% 1.34/0.57    ( ! [X45] : (~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | sK10 = X45 | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f232,f66])).
% 1.34/0.57  fof(f232,plain,(
% 1.34/0.57    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | sK10 = X45 | ~v1_funct_1(sK10) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f211,f67])).
% 1.34/0.57  fof(f211,plain,(
% 1.34/0.57    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | sK10 = X45 | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.34/0.57    inference(resolution,[],[f94,f69])).
% 1.34/0.57  fof(f94,plain,(
% 1.34/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f45])).
% 1.34/0.57  fof(f45,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.34/0.57    inference(nnf_transformation,[],[f15])).
% 1.34/0.57  fof(f15,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.34/0.57    inference(flattening,[],[f14])).
% 1.34/0.57  fof(f14,plain,(
% 1.34/0.57    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.34/0.57    inference(ennf_transformation,[],[f1])).
% 1.34/0.57  fof(f1,axiom,(
% 1.34/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.34/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.34/0.57  fof(f275,plain,(
% 1.34/0.57    ~spl11_10 | spl11_9),
% 1.34/0.57    inference(avatar_split_clause,[],[f270,f266,f272])).
% 1.34/0.57  fof(f270,plain,(
% 1.34/0.57    sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.34/0.57    inference(resolution,[],[f242,f123])).
% 1.34/0.57  fof(f123,plain,(
% 1.34/0.57    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)),
% 1.34/0.57    inference(forward_demodulation,[],[f71,f70])).
% 1.34/0.57  fof(f71,plain,(
% 1.34/0.57    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f242,plain,(
% 1.34/0.57    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f241,f96])).
% 1.34/0.57  fof(f241,plain,(
% 1.34/0.57    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3)) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f236,f97])).
% 1.34/0.57  fof(f236,plain,(
% 1.34/0.57    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | ~v1_funct_2(k3_tmap_1(X1,sK6,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3)) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.34/0.57    inference(resolution,[],[f231,f98])).
% 1.34/0.57  fof(f231,plain,(
% 1.34/0.57    ( ! [X44] : (~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sK9 = X44 | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f230,f62])).
% 1.34/0.57  fof(f230,plain,(
% 1.34/0.57    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | sK9 = X44 | ~v1_funct_1(sK9) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f210,f63])).
% 1.34/0.57  fof(f210,plain,(
% 1.34/0.57    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | sK9 = X44 | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(sK9) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.34/0.57    inference(resolution,[],[f94,f65])).
% 1.34/0.57  fof(f170,plain,(
% 1.34/0.57    spl11_5),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f169])).
% 1.34/0.57  fof(f169,plain,(
% 1.34/0.57    $false | spl11_5),
% 1.34/0.57    inference(subsumption_resolution,[],[f168,f50])).
% 1.34/0.57  fof(f168,plain,(
% 1.34/0.57    v2_struct_0(sK5) | spl11_5),
% 1.34/0.57    inference(subsumption_resolution,[],[f167,f52])).
% 1.34/0.57  fof(f167,plain,(
% 1.34/0.57    ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.34/0.57    inference(subsumption_resolution,[],[f166,f56])).
% 1.34/0.57  fof(f166,plain,(
% 1.34/0.57    v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.34/0.57    inference(subsumption_resolution,[],[f165,f58])).
% 1.34/0.57  fof(f165,plain,(
% 1.34/0.57    ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.34/0.57    inference(subsumption_resolution,[],[f164,f59])).
% 1.34/0.57  fof(f164,plain,(
% 1.34/0.57    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.34/0.57    inference(subsumption_resolution,[],[f163,f61])).
% 1.34/0.57  fof(f163,plain,(
% 1.34/0.57    ~m1_pre_topc(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.34/0.57    inference(resolution,[],[f93,f130])).
% 1.34/0.57  fof(f130,plain,(
% 1.34/0.57    ~sP2(sK5,sK8,sK7) | spl11_5),
% 1.34/0.57    inference(avatar_component_clause,[],[f128])).
% 1.34/0.57  fof(f128,plain,(
% 1.34/0.57    spl11_5 <=> sP2(sK5,sK8,sK7)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.34/0.57  fof(f93,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f24])).
% 1.34/0.57  fof(f24,plain,(
% 1.34/0.57    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(definition_folding,[],[f13,f23])).
% 1.34/0.57  fof(f23,plain,(
% 1.34/0.57    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.34/0.57  fof(f13,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.57    inference(flattening,[],[f12])).
% 1.34/0.57  fof(f12,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f3])).
% 1.34/0.57  fof(f3,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.34/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.34/0.57  fof(f141,plain,(
% 1.34/0.57    ~spl11_5 | spl11_7),
% 1.34/0.57    inference(avatar_split_clause,[],[f136,f138,f128])).
% 1.34/0.57  fof(f136,plain,(
% 1.34/0.57    m1_pre_topc(sK5,sK5) | ~sP2(sK5,sK8,sK7)),
% 1.34/0.57    inference(superposition,[],[f92,f70])).
% 1.34/0.57  fof(f92,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP2(X0,X1,X2)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f44])).
% 1.34/0.57  fof(f44,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP2(X0,X1,X2))),
% 1.34/0.57    inference(rectify,[],[f43])).
% 1.34/0.57  fof(f43,plain,(
% 1.34/0.57    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f23])).
% 1.34/0.57  fof(f122,plain,(
% 1.34/0.57    ~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4),
% 1.34/0.57    inference(avatar_split_clause,[],[f73,f119,f115,f111,f107])).
% 1.34/0.57  fof(f73,plain,(
% 1.34/0.57    ~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  % SZS output end Proof for theBenchmark
% 1.34/0.57  % (5136)------------------------------
% 1.34/0.57  % (5136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (5136)Termination reason: Refutation
% 1.34/0.57  
% 1.34/0.57  % (5136)Memory used [KB]: 6908
% 1.34/0.57  % (5136)Time elapsed: 0.152 s
% 1.34/0.57  % (5136)------------------------------
% 1.34/0.57  % (5136)------------------------------
% 1.34/0.57  % (5129)Success in time 0.211 s
%------------------------------------------------------------------------------

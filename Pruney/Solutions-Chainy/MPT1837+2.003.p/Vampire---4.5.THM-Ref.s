%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  236 (1465 expanded)
%              Number of leaves         :   31 ( 737 expanded)
%              Depth                    :   24
%              Number of atoms          : 1676 (36572 expanded)
%              Number of equality atoms :   42 (1651 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f828,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f245,f293,f444,f453,f625,f637,f645,f653,f656,f659,f805,f815,f821,f825])).

fof(f825,plain,
    ( spl10_4
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | spl10_4
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f822,f635])).

fof(f635,plain,
    ( sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f634])).

fof(f634,plain,
    ( spl10_14
  <=> sP3(sK5,sK7,sK6,sK4,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f822,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_4 ),
    inference(resolution,[],[f117,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(superposition,[],[f98,f68])).

fof(f68,plain,(
    sK4 = k1_tsep_1(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    & v1_tsep_1(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & v1_tsep_1(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f10,f34,f33,f32,f31,f30,f29])).

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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
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
                  & v1_tsep_1(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & v1_tsep_1(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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
                & v1_tsep_1(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & v1_tsep_1(X2,sK4)
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
              & v1_tsep_1(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & v1_tsep_1(X2,sK4)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
            & v1_tsep_1(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & v1_tsep_1(X2,sK4)
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
          & v1_tsep_1(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & v1_tsep_1(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
        & v1_tsep_1(X3,sK4)
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
      & v1_tsep_1(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f10,plain,(
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
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

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
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_tmap_1)).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP3(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP3(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f117,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_4
  <=> m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f821,plain,
    ( spl10_3
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f817,f349,f111])).

fof(f111,plain,
    ( spl10_3
  <=> v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f349,plain,
    ( spl10_10
  <=> sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f817,plain,
    ( v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)
    | ~ spl10_10 ),
    inference(resolution,[],[f350,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK7,sK6,sK4,X0)
      | v5_pre_topc(X0,sK4,X1) ) ),
    inference(superposition,[],[f84,f68])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f350,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f349])).

fof(f815,plain,
    ( spl10_10
    | ~ spl10_5
    | ~ spl10_13
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f814,f634,f442,f232,f349])).

fof(f232,plain,
    ( spl10_5
  <=> sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f442,plain,
    ( spl10_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
        | sP0(X1,sK7,sK6,sK4,X0)
        | ~ sP1(X1,sK7,X0,sK6,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f814,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_5
    | ~ spl10_13
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f813,f635])).

fof(f813,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f808,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f808,plain,
    ( sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | v2_struct_0(sK5)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f807,f53])).

fof(f53,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f807,plain,
    ( ~ l1_pre_topc(sK5)
    | sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | v2_struct_0(sK5)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f806,f52])).

fof(f52,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f806,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | v2_struct_0(sK5)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(resolution,[],[f233,f460])).

fof(f460,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
        | v2_struct_0(X0)
        | ~ sP3(X0,sK7,sK6,sK4,X2,X1) )
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f459,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0))
      | ~ sP3(X0,sK7,sK6,sK4,X2,X1) ) ),
    inference(superposition,[],[f97,f68])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f459,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0))
        | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
        | ~ sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4)
        | ~ sP3(X0,sK7,sK6,sK4,X2,X1) )
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f454,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f454,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
        | ~ v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0))
        | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2))
        | ~ sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4)
        | ~ sP3(X0,sK7,sK6,sK4,X2,X1) )
    | ~ spl10_13 ),
    inference(resolution,[],[f443,f163])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
        | sP0(X1,sK7,sK6,sK4,X0)
        | ~ sP1(X1,sK7,X0,sK6,sK4) )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f442])).

fof(f233,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f232])).

fof(f805,plain,
    ( spl10_5
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f804,f290,f236,f232])).

fof(f236,plain,
    ( spl10_6
  <=> sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f290,plain,
    ( spl10_9
  <=> sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f804,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f803,f60])).

fof(f60,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f803,plain,
    ( ~ v1_funct_1(sK8)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f802,f238])).

fof(f238,plain,
    ( sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f236])).

fof(f802,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f801,f61])).

fof(f61,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f801,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f800,f238])).

fof(f800,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f799,f62])).

fof(f62,plain,(
    v5_pre_topc(sK8,sK6,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f799,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK5)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f798,f238])).

fof(f798,plain,
    ( sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f797,f63])).

fof(f63,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f797,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f786,f238])).

fof(f786,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f785,f64])).

fof(f64,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f785,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f784,f65])).

fof(f65,plain,(
    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f784,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f783,f66])).

fof(f66,plain,(
    v5_pre_topc(sK9,sK7,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f783,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
    | ~ v5_pre_topc(sK9,sK7,sK5)
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK9)
    | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)
    | ~ v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5))
    | ~ v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f780,f67])).

fof(f67,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f780,plain,
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
    inference(superposition,[],[f565,f292])).

fof(f292,plain,
    ( sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f290])).

fof(f565,plain,(
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
    inference(superposition,[],[f81,f68])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f659,plain,
    ( spl10_2
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | spl10_2
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f657,f635])).

fof(f657,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_2 ),
    inference(resolution,[],[f109,f161])).

fof(f109,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_2
  <=> v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f656,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | spl10_11 ),
    inference(subsumption_resolution,[],[f654,f50])).

fof(f50,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f654,plain,
    ( ~ l1_pre_topc(sK4)
    | spl10_11 ),
    inference(resolution,[],[f355,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f355,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl10_11
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f653,plain,(
    spl10_14 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | spl10_14 ),
    inference(subsumption_resolution,[],[f651,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f651,plain,
    ( v2_struct_0(sK4)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f650,f49])).

fof(f49,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f650,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f649,f50])).

fof(f649,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f648,f56])).

fof(f56,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f648,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f647,f59])).

fof(f59,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f647,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_14 ),
    inference(resolution,[],[f636,f592])).

fof(f592,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f591,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f591,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f590,f60])).

fof(f590,plain,(
    ! [X0] :
      ( sP3(sK5,sK7,sK6,X0,sK9,sK8)
      | ~ v1_funct_1(sK8)
      | ~ m1_pre_topc(sK7,X0)
      | ~ m1_pre_topc(sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f577,f61])).

fof(f577,plain,(
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
    inference(resolution,[],[f518,f63])).

fof(f518,plain,(
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
    inference(subsumption_resolution,[],[f517,f51])).

fof(f517,plain,(
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
    inference(subsumption_resolution,[],[f516,f52])).

fof(f516,plain,(
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
    inference(subsumption_resolution,[],[f515,f53])).

fof(f515,plain,(
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
    inference(subsumption_resolution,[],[f514,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f514,plain,(
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
    inference(subsumption_resolution,[],[f513,f64])).

fof(f513,plain,(
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
    inference(subsumption_resolution,[],[f484,f65])).

fof(f484,plain,(
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
    inference(resolution,[],[f99,f67])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(definition_folding,[],[f21,f27])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f636,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f634])).

fof(f645,plain,
    ( ~ spl10_14
    | ~ spl10_11
    | spl10_7 ),
    inference(avatar_split_clause,[],[f644,f242,f353,f634])).

fof(f242,plain,
    ( spl10_7
  <=> sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f644,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f643,f48])).

fof(f643,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f642,f49])).

fof(f642,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f641,f50])).

fof(f641,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f640,f51])).

fof(f640,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f639,f52])).

fof(f639,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f638,f53])).

fof(f638,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f407,f56])).

fof(f407,plain,
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
    inference(resolution,[],[f310,f244])).

fof(f244,plain,
    ( ~ sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f242])).

fof(f310,plain,(
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
    inference(subsumption_resolution,[],[f309,f96])).

fof(f309,plain,(
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
    inference(subsumption_resolution,[],[f296,f161])).

fof(f296,plain,(
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
    inference(resolution,[],[f95,f163])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(definition_folding,[],[f19,f25])).

fof(f25,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP2(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f637,plain,
    ( ~ spl10_14
    | ~ spl10_11
    | spl10_8 ),
    inference(avatar_split_clause,[],[f632,f286,f353,f634])).

fof(f286,plain,
    ( spl10_8
  <=> sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f632,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f631,f48])).

fof(f631,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f630,f49])).

fof(f630,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f629,f50])).

fof(f629,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f628,f51])).

fof(f628,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f627,f52])).

fof(f627,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_8 ),
    inference(subsumption_resolution,[],[f626,f53])).

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
    inference(subsumption_resolution,[],[f408,f59])).

fof(f408,plain,
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
    inference(resolution,[],[f310,f288])).

fof(f288,plain,
    ( ~ sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f286])).

fof(f625,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f623,f48])).

fof(f623,plain,
    ( v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f622,f49])).

fof(f622,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f621,f50])).

fof(f621,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f620,f56])).

fof(f620,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f619,f59])).

fof(f619,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_1 ),
    inference(resolution,[],[f592,f123])).

fof(f123,plain,
    ( ~ sP3(sK5,sK7,sK6,sK4,sK9,sK8)
    | spl10_1 ),
    inference(resolution,[],[f96,f105])).

fof(f105,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_1
  <=> v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f453,plain,(
    spl10_12 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | spl10_12 ),
    inference(subsumption_resolution,[],[f451,f48])).

fof(f451,plain,
    ( v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f450,f49])).

fof(f450,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f449,f50])).

fof(f449,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f448,f55])).

fof(f55,plain,(
    v1_tsep_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f448,plain,
    ( ~ v1_tsep_1(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f447,f56])).

fof(f447,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ v1_tsep_1(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f446,f58])).

fof(f58,plain,(
    v1_tsep_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f446,plain,
    ( ~ v1_tsep_1(sK7,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ v1_tsep_1(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(subsumption_resolution,[],[f445,f59])).

fof(f445,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ v1_tsep_1(sK7,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ v1_tsep_1(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl10_12 ),
    inference(resolution,[],[f440,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).

fof(f440,plain,
    ( ~ r4_tsep_1(sK4,sK6,sK7)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl10_12
  <=> r4_tsep_1(sK4,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f444,plain,
    ( ~ spl10_12
    | spl10_13 ),
    inference(avatar_split_clause,[],[f436,f442,f438])).

fof(f436,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f435,f48])).

fof(f435,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f434,f49])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f433,f50])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f432,f54])).

fof(f432,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f431,f56])).

fof(f431,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | ~ m1_pre_topc(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f430,f57])).

fof(f430,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f421,f59])).

fof(f421,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ sP1(X1,sK7,X0,sK6,sK4)
      | sP0(X1,sK7,sK6,sK4,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK4,sK6,sK7)
      | ~ m1_pre_topc(sK7,sK4)
      | v2_struct_0(sK7)
      | ~ m1_pre_topc(sK6,sK4)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(superposition,[],[f88,f68])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ sP1(X1,X3,X4,X2,X0)
      | sP0(X1,X3,X2,X0,X4)
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(definition_folding,[],[f13,f23,f22])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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

fof(f293,plain,
    ( ~ spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f284,f290,f286])).

fof(f284,plain,
    ( sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    inference(resolution,[],[f225,f120])).

fof(f120,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) ),
    inference(forward_demodulation,[],[f70,f68])).

fof(f70,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f225,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9)
      | sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3)
      | ~ sP2(sK5,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f224,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP2(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f224,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9)
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3))
      | ~ sP2(sK5,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f219,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f219,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9)
      | ~ v1_funct_2(k3_tmap_1(X1,sK5,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3))
      | ~ sP2(sK5,sK7,X3,X2,X1) ) ),
    inference(resolution,[],[f203,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f203,plain,(
    ! [X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      | sK9 = X45
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9)
      | ~ v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f202,f64])).

fof(f202,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9)
      | sK9 = X45
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      | ~ v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f181,f65])).

fof(f181,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9)
      | sK9 = X45
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      | ~ v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5))
      | ~ v1_funct_1(X45) ) ),
    inference(resolution,[],[f90,f67])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f245,plain,
    ( ~ spl10_7
    | spl10_6 ),
    inference(avatar_split_clause,[],[f240,f236,f242])).

fof(f240,plain,
    ( sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))
    | ~ sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) ),
    inference(resolution,[],[f212,f119])).

fof(f119,plain,(
    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) ),
    inference(forward_demodulation,[],[f69,f68])).

fof(f69,plain,(
    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f212,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8)
      | sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3)
      | ~ sP2(sK5,sK6,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f211,f92])).

fof(f211,plain,(
    ! [X2,X3,X1] :
      ( sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3)
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8)
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3))
      | ~ sP2(sK5,sK6,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f206,f93])).

fof(f206,plain,(
    ! [X2,X3,X1] :
      ( sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3)
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8)
      | ~ v1_funct_2(k3_tmap_1(X1,sK5,X2,sK6,X3),u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3))
      | ~ sP2(sK5,sK6,X3,X2,X1) ) ),
    inference(resolution,[],[f201,f94])).

fof(f201,plain,(
    ! [X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | sK8 = X44
      | ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8)
      | ~ v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f200,f60])).

fof(f200,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8)
      | sK8 = X44
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f180,f61])).

fof(f180,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8)
      | sK8 = X44
      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(sK8)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))
      | ~ v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5))
      | ~ v1_funct_1(X44) ) ),
    inference(resolution,[],[f90,f63])).

fof(f118,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f71,f115,f111,f107,f103])).

fof(f71,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:02:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (31178)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (31180)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (31176)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (31183)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (31181)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (31179)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (31200)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (31195)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (31192)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (31186)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (31201)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (31194)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (31177)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31185)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (31190)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (31184)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (31187)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (31191)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (31197)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (31188)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (31199)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (31182)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (31189)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (31198)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (31196)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (31193)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.57  % (31180)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f828,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(avatar_sat_refutation,[],[f118,f245,f293,f444,f453,f625,f637,f645,f653,f656,f659,f805,f815,f821,f825])).
% 1.73/0.59  fof(f825,plain,(
% 1.73/0.59    spl10_4 | ~spl10_14),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f824])).
% 1.73/0.59  fof(f824,plain,(
% 1.73/0.59    $false | (spl10_4 | ~spl10_14)),
% 1.73/0.59    inference(subsumption_resolution,[],[f822,f635])).
% 1.73/0.59  fof(f635,plain,(
% 1.73/0.59    sP3(sK5,sK7,sK6,sK4,sK9,sK8) | ~spl10_14),
% 1.73/0.59    inference(avatar_component_clause,[],[f634])).
% 1.73/0.59  fof(f634,plain,(
% 1.73/0.59    spl10_14 <=> sP3(sK5,sK7,sK6,sK4,sK9,sK8)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.73/0.59  fof(f822,plain,(
% 1.73/0.59    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_4),
% 1.73/0.59    inference(resolution,[],[f117,f163])).
% 1.73/0.59  fof(f163,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 1.73/0.59    inference(superposition,[],[f98,f68])).
% 1.73/0.59  fof(f68,plain,(
% 1.73/0.59    sK4 = k1_tsep_1(sK4,sK6,sK7)),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    ((((((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(sK9,sK7,sK5) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(sK8,sK6,sK5) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & v1_tsep_1(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & v1_tsep_1(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f10,f34,f33,f32,f31,f30,f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK4,X1,X2,X3,X4,X5),sK4,X1) | ~v1_funct_2(k10_tmap_1(sK4,X1,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f30,plain,(
% 1.73/0.59    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK4,X1,X2,X3,X4,X5),sK4,X1) | ~v1_funct_2(k10_tmap_1(sK4,X1,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK4,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK4,X1,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,X1,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5)))) & v5_pre_topc(X4,X2,sK5) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,X2,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X3,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,X2,X3),X2,k10_tmap_1(sK4,sK5,X2,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5)))) & v5_pre_topc(X4,X2,sK5) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),X3,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),sK6,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,sK4) & v1_tsep_1(sK6,sK4) & ~v2_struct_0(sK6))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f32,plain,(
% 1.73/0.59    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),X3,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,X3),sK6,k10_tmap_1(sK4,sK5,sK6,X3,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v5_pre_topc(X5,X3,sK5) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(sK7,sK4) & v1_tsep_1(sK7,sK4) & ~v2_struct_0(sK7))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f33,plain,(
% 1.73/0.59    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,X4,X5)),X4) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(X4,sK6,sK5) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) & v5_pre_topc(sK8,sK6,sK5) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) & v1_funct_1(sK8))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),X5) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,X5)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(X5,sK7,sK5) & v1_funct_2(X5,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9) & r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8) & sK4 = k1_tsep_1(sK4,sK6,sK7) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v5_pre_topc(sK9,sK7,sK5) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK9))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f10,plain,(
% 1.73/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f9])).
% 1.73/0.59  fof(f9,plain,(
% 1.73/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f8])).
% 1.73/0.59  fof(f8,negated_conjecture,(
% 1.73/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.73/0.59    inference(negated_conjecture,[],[f7])).
% 1.73/0.59  fof(f7,conjecture,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_tmap_1)).
% 1.73/0.59  fof(f98,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f47])).
% 1.73/0.59  fof(f47,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP3(X0,X1,X2,X3,X4,X5))),
% 1.73/0.59    inference(rectify,[],[f46])).
% 1.73/0.59  fof(f46,plain,(
% 1.73/0.59    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP3(X1,X3,X2,X0,X5,X4))),
% 1.73/0.59    inference(nnf_transformation,[],[f27])).
% 1.73/0.59  fof(f27,plain,(
% 1.73/0.59    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP3(X1,X3,X2,X0,X5,X4))),
% 1.73/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.73/0.59  fof(f117,plain,(
% 1.73/0.59    ~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | spl10_4),
% 1.73/0.59    inference(avatar_component_clause,[],[f115])).
% 1.73/0.59  fof(f115,plain,(
% 1.73/0.59    spl10_4 <=> m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.73/0.59  fof(f821,plain,(
% 1.73/0.59    spl10_3 | ~spl10_10),
% 1.73/0.59    inference(avatar_split_clause,[],[f817,f349,f111])).
% 1.73/0.59  fof(f111,plain,(
% 1.73/0.59    spl10_3 <=> v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.73/0.59  fof(f349,plain,(
% 1.73/0.59    spl10_10 <=> sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.73/0.59  fof(f817,plain,(
% 1.73/0.59    v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~spl10_10),
% 1.73/0.59    inference(resolution,[],[f350,f121])).
% 1.73/0.59  fof(f121,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~sP0(X1,sK7,sK6,sK4,X0) | v5_pre_topc(X0,sK4,X1)) )),
% 1.73/0.59    inference(superposition,[],[f84,f68])).
% 1.73/0.59  fof(f84,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f41])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.73/0.59    inference(rectify,[],[f40])).
% 1.73/0.59  fof(f40,plain,(
% 1.73/0.59    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.73/0.59    inference(flattening,[],[f39])).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.73/0.59    inference(nnf_transformation,[],[f22])).
% 1.73/0.59  fof(f22,plain,(
% 1.73/0.59    ! [X1,X3,X2,X0,X4] : (sP0(X1,X3,X2,X0,X4) <=> (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))),
% 1.73/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.73/0.59  fof(f350,plain,(
% 1.73/0.59    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~spl10_10),
% 1.73/0.59    inference(avatar_component_clause,[],[f349])).
% 1.73/0.59  fof(f815,plain,(
% 1.73/0.59    spl10_10 | ~spl10_5 | ~spl10_13 | ~spl10_14),
% 1.73/0.59    inference(avatar_split_clause,[],[f814,f634,f442,f232,f349])).
% 1.73/0.59  fof(f232,plain,(
% 1.73/0.59    spl10_5 <=> sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.73/0.59  fof(f442,plain,(
% 1.73/0.59    spl10_13 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | sP0(X1,sK7,sK6,sK4,X0) | ~sP1(X1,sK7,X0,sK6,sK4))),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.73/0.59  fof(f814,plain,(
% 1.73/0.59    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | (~spl10_5 | ~spl10_13 | ~spl10_14)),
% 1.73/0.59    inference(subsumption_resolution,[],[f813,f635])).
% 1.73/0.59  fof(f813,plain,(
% 1.73/0.59    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | (~spl10_5 | ~spl10_13)),
% 1.73/0.59    inference(subsumption_resolution,[],[f808,f51])).
% 1.73/0.59  fof(f51,plain,(
% 1.73/0.59    ~v2_struct_0(sK5)),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f808,plain,(
% 1.73/0.59    sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | v2_struct_0(sK5) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | (~spl10_5 | ~spl10_13)),
% 1.73/0.59    inference(subsumption_resolution,[],[f807,f53])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    l1_pre_topc(sK5)),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f807,plain,(
% 1.73/0.59    ~l1_pre_topc(sK5) | sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | v2_struct_0(sK5) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | (~spl10_5 | ~spl10_13)),
% 1.73/0.59    inference(subsumption_resolution,[],[f806,f52])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    v2_pre_topc(sK5)),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f806,plain,(
% 1.73/0.59    ~v2_pre_topc(sK5) | ~l1_pre_topc(sK5) | sP0(sK5,sK7,sK6,sK4,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | v2_struct_0(sK5) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | (~spl10_5 | ~spl10_13)),
% 1.73/0.59    inference(resolution,[],[f233,f460])).
% 1.73/0.59  fof(f460,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | v2_struct_0(X0) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) ) | ~spl10_13),
% 1.73/0.59    inference(subsumption_resolution,[],[f459,f161])).
% 1.73/0.59  fof(f161,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0)) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) )),
% 1.73/0.59    inference(superposition,[],[f97,f68])).
% 1.73/0.59  fof(f97,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f47])).
% 1.73/0.59  fof(f459,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0)) | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) ) | ~spl10_13),
% 1.73/0.59    inference(subsumption_resolution,[],[f454,f96])).
% 1.73/0.59  fof(f96,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f47])).
% 1.73/0.60  fof(f454,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~v1_funct_2(k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),u1_struct_0(sK4),u1_struct_0(X0)) | sP0(X0,sK7,sK6,sK4,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2)) | ~sP1(X0,sK7,k10_tmap_1(sK4,X0,sK6,sK7,X1,X2),sK6,sK4) | ~sP3(X0,sK7,sK6,sK4,X2,X1)) ) | ~spl10_13),
% 1.73/0.60    inference(resolution,[],[f443,f163])).
% 1.73/0.60  fof(f443,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | sP0(X1,sK7,sK6,sK4,X0) | ~sP1(X1,sK7,X0,sK6,sK4)) ) | ~spl10_13),
% 1.73/0.60    inference(avatar_component_clause,[],[f442])).
% 1.73/0.60  fof(f233,plain,(
% 1.73/0.60    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~spl10_5),
% 1.73/0.60    inference(avatar_component_clause,[],[f232])).
% 1.73/0.60  fof(f805,plain,(
% 1.73/0.60    spl10_5 | ~spl10_6 | ~spl10_9),
% 1.73/0.60    inference(avatar_split_clause,[],[f804,f290,f236,f232])).
% 1.73/0.60  fof(f236,plain,(
% 1.73/0.60    spl10_6 <=> sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.73/0.60  fof(f290,plain,(
% 1.73/0.60    spl10_9 <=> sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.73/0.60  fof(f804,plain,(
% 1.73/0.60    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(subsumption_resolution,[],[f803,f60])).
% 1.73/0.60  fof(f60,plain,(
% 1.73/0.60    v1_funct_1(sK8)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f803,plain,(
% 1.73/0.60    ~v1_funct_1(sK8) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(forward_demodulation,[],[f802,f238])).
% 1.73/0.60  fof(f238,plain,(
% 1.73/0.60    sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~spl10_6),
% 1.73/0.60    inference(avatar_component_clause,[],[f236])).
% 1.73/0.60  fof(f802,plain,(
% 1.73/0.60    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(subsumption_resolution,[],[f801,f61])).
% 1.73/0.60  fof(f61,plain,(
% 1.73/0.60    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5))),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f801,plain,(
% 1.73/0.60    ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(forward_demodulation,[],[f800,f238])).
% 1.73/0.60  fof(f800,plain,(
% 1.73/0.60    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(subsumption_resolution,[],[f799,f62])).
% 1.73/0.60  fof(f62,plain,(
% 1.73/0.60    v5_pre_topc(sK8,sK6,sK5)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f799,plain,(
% 1.73/0.60    ~v5_pre_topc(sK8,sK6,sK5) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(forward_demodulation,[],[f798,f238])).
% 1.73/0.60  fof(f798,plain,(
% 1.73/0.60    sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(subsumption_resolution,[],[f797,f63])).
% 1.73/0.60  fof(f63,plain,(
% 1.73/0.60    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5))))),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f797,plain,(
% 1.73/0.60    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | (~spl10_6 | ~spl10_9)),
% 1.73/0.60    inference(forward_demodulation,[],[f786,f238])).
% 1.73/0.60  fof(f786,plain,(
% 1.73/0.60    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 1.73/0.60    inference(subsumption_resolution,[],[f785,f64])).
% 1.73/0.60  fof(f64,plain,(
% 1.73/0.60    v1_funct_1(sK9)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f785,plain,(
% 1.73/0.60    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 1.73/0.60    inference(subsumption_resolution,[],[f784,f65])).
% 1.73/0.60  fof(f65,plain,(
% 1.73/0.60    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5))),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f784,plain,(
% 1.73/0.60    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 1.73/0.60    inference(subsumption_resolution,[],[f783,f66])).
% 1.73/0.60  fof(f66,plain,(
% 1.73/0.60    v5_pre_topc(sK9,sK7,sK5)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f783,plain,(
% 1.73/0.60    ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v5_pre_topc(sK9,sK7,sK5) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 1.73/0.60    inference(subsumption_resolution,[],[f780,f67])).
% 1.73/0.60  fof(f67,plain,(
% 1.73/0.60    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f780,plain,(
% 1.73/0.60    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~m1_subset_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v5_pre_topc(sK9,sK7,sK5) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | sP1(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK6,sK5) | ~v1_funct_2(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))) | ~spl10_9),
% 1.73/0.60    inference(superposition,[],[f565,f292])).
% 1.73/0.60  fof(f292,plain,(
% 1.73/0.60    sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~spl10_9),
% 1.73/0.60    inference(avatar_component_clause,[],[f290])).
% 1.73/0.60  fof(f565,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK4,X0,sK4,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK4,X0,sK4,sK6,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(sK4,X0,sK4,sK7,X1),sK7,X0) | ~v1_funct_2(k3_tmap_1(sK4,X0,sK4,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK4,X0,sK4,sK7,X1)) | sP1(X0,sK7,X1,sK6,sK4) | ~v5_pre_topc(k3_tmap_1(sK4,X0,sK4,sK6,X1),sK6,X0) | ~v1_funct_2(k3_tmap_1(sK4,X0,sK4,sK6,X1),u1_struct_0(sK6),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK4,X0,sK4,sK6,X1))) )),
% 1.73/0.60    inference(superposition,[],[f81,f68])).
% 1.73/0.60  fof(f81,plain,(
% 1.73/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP1(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f38])).
% 1.73/0.60  fof(f38,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.73/0.60    inference(rectify,[],[f37])).
% 1.73/0.60  fof(f37,plain,(
% 1.73/0.60    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.73/0.60    inference(flattening,[],[f36])).
% 1.73/0.60  fof(f36,plain,(
% 1.73/0.60    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.73/0.60    inference(nnf_transformation,[],[f23])).
% 1.73/0.60  fof(f23,plain,(
% 1.73/0.60    ! [X1,X3,X4,X2,X0] : (sP1(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 1.73/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.73/0.60  fof(f659,plain,(
% 1.73/0.60    spl10_2 | ~spl10_14),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f658])).
% 1.73/0.60  fof(f658,plain,(
% 1.73/0.60    $false | (spl10_2 | ~spl10_14)),
% 1.73/0.60    inference(subsumption_resolution,[],[f657,f635])).
% 1.73/0.60  fof(f657,plain,(
% 1.73/0.60    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_2),
% 1.73/0.60    inference(resolution,[],[f109,f161])).
% 1.73/0.60  fof(f109,plain,(
% 1.73/0.60    ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | spl10_2),
% 1.73/0.60    inference(avatar_component_clause,[],[f107])).
% 1.73/0.60  fof(f107,plain,(
% 1.73/0.60    spl10_2 <=> v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.73/0.60  fof(f656,plain,(
% 1.73/0.60    spl10_11),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f655])).
% 1.73/0.60  fof(f655,plain,(
% 1.73/0.60    $false | spl10_11),
% 1.73/0.60    inference(subsumption_resolution,[],[f654,f50])).
% 1.73/0.60  fof(f50,plain,(
% 1.73/0.60    l1_pre_topc(sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f654,plain,(
% 1.73/0.60    ~l1_pre_topc(sK4) | spl10_11),
% 1.73/0.60    inference(resolution,[],[f355,f72])).
% 1.73/0.60  fof(f72,plain,(
% 1.73/0.60    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f11])).
% 1.73/0.60  fof(f11,plain,(
% 1.73/0.60    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f5])).
% 1.73/0.60  fof(f5,axiom,(
% 1.73/0.60    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.73/0.60  fof(f355,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | spl10_11),
% 1.73/0.60    inference(avatar_component_clause,[],[f353])).
% 1.73/0.60  fof(f353,plain,(
% 1.73/0.60    spl10_11 <=> m1_pre_topc(sK4,sK4)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.73/0.60  fof(f653,plain,(
% 1.73/0.60    spl10_14),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f652])).
% 1.73/0.60  fof(f652,plain,(
% 1.73/0.60    $false | spl10_14),
% 1.73/0.60    inference(subsumption_resolution,[],[f651,f48])).
% 1.73/0.60  fof(f48,plain,(
% 1.73/0.60    ~v2_struct_0(sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f651,plain,(
% 1.73/0.60    v2_struct_0(sK4) | spl10_14),
% 1.73/0.60    inference(subsumption_resolution,[],[f650,f49])).
% 1.73/0.60  fof(f49,plain,(
% 1.73/0.60    v2_pre_topc(sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f650,plain,(
% 1.73/0.60    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_14),
% 1.73/0.60    inference(subsumption_resolution,[],[f649,f50])).
% 1.73/0.60  fof(f649,plain,(
% 1.73/0.60    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_14),
% 1.73/0.60    inference(subsumption_resolution,[],[f648,f56])).
% 1.73/0.60  fof(f56,plain,(
% 1.73/0.60    m1_pre_topc(sK6,sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f648,plain,(
% 1.73/0.60    ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_14),
% 1.73/0.60    inference(subsumption_resolution,[],[f647,f59])).
% 1.73/0.60  fof(f59,plain,(
% 1.73/0.60    m1_pre_topc(sK7,sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f647,plain,(
% 1.73/0.60    ~m1_pre_topc(sK7,sK4) | ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_14),
% 1.73/0.60    inference(resolution,[],[f636,f592])).
% 1.73/0.60  fof(f592,plain,(
% 1.73/0.60    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f591,f54])).
% 1.73/0.60  fof(f54,plain,(
% 1.73/0.60    ~v2_struct_0(sK6)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f591,plain,(
% 1.73/0.60    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK6) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f590,f60])).
% 1.73/0.60  fof(f590,plain,(
% 1.73/0.60    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK6) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f577,f61])).
% 1.73/0.60  fof(f577,plain,(
% 1.73/0.60    ( ! [X0] : (sP3(sK5,sK7,sK6,X0,sK9,sK8) | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_pre_topc(sK7,X0) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK6) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(resolution,[],[f518,f63])).
% 1.73/0.60  fof(f518,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | sP3(sK5,sK7,X65,X66,sK9,X67) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f517,f51])).
% 1.73/0.60  fof(f517,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f516,f52])).
% 1.73/0.60  fof(f516,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f515,f53])).
% 1.73/0.60  fof(f515,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f514,f57])).
% 1.73/0.60  fof(f57,plain,(
% 1.73/0.60    ~v2_struct_0(sK7)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f514,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | v2_struct_0(sK7) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f513,f64])).
% 1.73/0.60  fof(f513,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~v1_funct_1(sK9) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | v2_struct_0(sK7) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f484,f65])).
% 1.73/0.60  fof(f484,plain,(
% 1.73/0.60    ( ! [X66,X67,X65] : (sP3(sK5,sK7,X65,X66,sK9,X67) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK5)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK5)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK7,X66) | v2_struct_0(sK7) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.73/0.60    inference(resolution,[],[f99,f67])).
% 1.73/0.60  fof(f99,plain,(
% 1.73/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP3(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f28])).
% 1.73/0.60  fof(f28,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4,X5] : (sP3(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(definition_folding,[],[f21,f27])).
% 1.73/0.60  fof(f21,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(flattening,[],[f20])).
% 1.73/0.60  fof(f20,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f2])).
% 1.73/0.60  fof(f2,axiom,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.73/0.60  fof(f636,plain,(
% 1.73/0.60    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_14),
% 1.73/0.60    inference(avatar_component_clause,[],[f634])).
% 1.73/0.60  fof(f645,plain,(
% 1.73/0.60    ~spl10_14 | ~spl10_11 | spl10_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f644,f242,f353,f634])).
% 1.73/0.60  fof(f242,plain,(
% 1.73/0.60    spl10_7 <=> sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.73/0.60  fof(f644,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f643,f48])).
% 1.73/0.60  fof(f643,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f642,f49])).
% 1.73/0.60  fof(f642,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f641,f50])).
% 1.73/0.60  fof(f641,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f640,f51])).
% 1.73/0.60  fof(f640,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f639,f52])).
% 1.73/0.60  fof(f639,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f638,f53])).
% 1.73/0.60  fof(f638,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(subsumption_resolution,[],[f407,f56])).
% 1.73/0.60  fof(f407,plain,(
% 1.73/0.60    ~m1_pre_topc(sK6,sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_7),
% 1.73/0.60    inference(resolution,[],[f310,f244])).
% 1.73/0.60  fof(f244,plain,(
% 1.73/0.60    ~sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) | spl10_7),
% 1.73/0.60    inference(avatar_component_clause,[],[f242])).
% 1.73/0.60  fof(f310,plain,(
% 1.73/0.60    ( ! [X12,X10,X8,X11,X9] : (sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK4,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP3(X8,sK7,sK6,sK4,X11,X10)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f309,f96])).
% 1.73/0.60  fof(f309,plain,(
% 1.73/0.60    ( ! [X12,X10,X8,X11,X9] : (sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12) | ~v1_funct_1(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK4,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP3(X8,sK7,sK6,sK4,X11,X10)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f296,f161])).
% 1.73/0.60  fof(f296,plain,(
% 1.73/0.60    ( ! [X12,X10,X8,X11,X9] : (sP2(X8,X9,k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),sK4,X12) | ~v1_funct_2(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11),u1_struct_0(sK4),u1_struct_0(X8)) | ~v1_funct_1(k10_tmap_1(sK4,X8,sK6,sK7,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK4,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP3(X8,sK7,sK6,sK4,X11,X10)) )),
% 1.73/0.60    inference(resolution,[],[f95,f163])).
% 1.73/0.60  fof(f95,plain,(
% 1.73/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP2(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f26])).
% 1.73/0.60  fof(f26,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4] : (sP2(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(definition_folding,[],[f19,f25])).
% 1.73/0.60  fof(f25,plain,(
% 1.73/0.60    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP2(X1,X3,X4,X2,X0))),
% 1.73/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.73/0.60  fof(f19,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(flattening,[],[f18])).
% 1.73/0.60  fof(f18,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f3])).
% 1.73/0.60  fof(f3,axiom,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.73/0.60  fof(f637,plain,(
% 1.73/0.60    ~spl10_14 | ~spl10_11 | spl10_8),
% 1.73/0.60    inference(avatar_split_clause,[],[f632,f286,f353,f634])).
% 1.73/0.60  fof(f286,plain,(
% 1.73/0.60    spl10_8 <=> sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.73/0.60  fof(f632,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f631,f48])).
% 1.73/0.60  fof(f631,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f630,f49])).
% 1.73/0.60  fof(f630,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f629,f50])).
% 1.73/0.60  fof(f629,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f628,f51])).
% 1.73/0.60  fof(f628,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f627,f52])).
% 1.73/0.60  fof(f627,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f626,f53])).
% 1.73/0.60  fof(f626,plain,(
% 1.73/0.60    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(subsumption_resolution,[],[f408,f59])).
% 1.73/0.60  fof(f408,plain,(
% 1.73/0.60    ~m1_pre_topc(sK7,sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_8),
% 1.73/0.60    inference(resolution,[],[f310,f288])).
% 1.73/0.60  fof(f288,plain,(
% 1.73/0.60    ~sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4) | spl10_8),
% 1.73/0.60    inference(avatar_component_clause,[],[f286])).
% 1.73/0.60  fof(f625,plain,(
% 1.73/0.60    spl10_1),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f624])).
% 1.73/0.60  fof(f624,plain,(
% 1.73/0.60    $false | spl10_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f623,f48])).
% 1.73/0.60  fof(f623,plain,(
% 1.73/0.60    v2_struct_0(sK4) | spl10_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f622,f49])).
% 1.73/0.60  fof(f622,plain,(
% 1.73/0.60    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f621,f50])).
% 1.73/0.60  fof(f621,plain,(
% 1.73/0.60    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f620,f56])).
% 1.73/0.60  fof(f620,plain,(
% 1.73/0.60    ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f619,f59])).
% 1.73/0.60  fof(f619,plain,(
% 1.73/0.60    ~m1_pre_topc(sK7,sK4) | ~m1_pre_topc(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_1),
% 1.73/0.60    inference(resolution,[],[f592,f123])).
% 1.73/0.60  fof(f123,plain,(
% 1.73/0.60    ~sP3(sK5,sK7,sK6,sK4,sK9,sK8) | spl10_1),
% 1.73/0.60    inference(resolution,[],[f96,f105])).
% 1.73/0.60  fof(f105,plain,(
% 1.73/0.60    ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | spl10_1),
% 1.73/0.60    inference(avatar_component_clause,[],[f103])).
% 1.73/0.60  fof(f103,plain,(
% 1.73/0.60    spl10_1 <=> v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.73/0.60  fof(f453,plain,(
% 1.73/0.60    spl10_12),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f452])).
% 1.73/0.60  fof(f452,plain,(
% 1.73/0.60    $false | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f451,f48])).
% 1.73/0.60  fof(f451,plain,(
% 1.73/0.60    v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f450,f49])).
% 1.73/0.60  fof(f450,plain,(
% 1.73/0.60    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f449,f50])).
% 1.73/0.60  fof(f449,plain,(
% 1.73/0.60    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f448,f55])).
% 1.73/0.60  fof(f55,plain,(
% 1.73/0.60    v1_tsep_1(sK6,sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f448,plain,(
% 1.73/0.60    ~v1_tsep_1(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f447,f56])).
% 1.73/0.60  fof(f447,plain,(
% 1.73/0.60    ~m1_pre_topc(sK6,sK4) | ~v1_tsep_1(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f446,f58])).
% 1.73/0.60  fof(f58,plain,(
% 1.73/0.60    v1_tsep_1(sK7,sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f446,plain,(
% 1.73/0.60    ~v1_tsep_1(sK7,sK4) | ~m1_pre_topc(sK6,sK4) | ~v1_tsep_1(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(subsumption_resolution,[],[f445,f59])).
% 1.73/0.60  fof(f445,plain,(
% 1.73/0.60    ~m1_pre_topc(sK7,sK4) | ~v1_tsep_1(sK7,sK4) | ~m1_pre_topc(sK6,sK4) | ~v1_tsep_1(sK6,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl10_12),
% 1.73/0.60    inference(resolution,[],[f440,f89])).
% 1.73/0.60  fof(f89,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f15])).
% 1.73/0.60  fof(f15,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(flattening,[],[f14])).
% 1.73/0.60  fof(f14,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f6])).
% 1.73/0.60  fof(f6,axiom,(
% 1.73/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).
% 1.73/0.60  fof(f440,plain,(
% 1.73/0.60    ~r4_tsep_1(sK4,sK6,sK7) | spl10_12),
% 1.73/0.60    inference(avatar_component_clause,[],[f438])).
% 1.73/0.60  fof(f438,plain,(
% 1.73/0.60    spl10_12 <=> r4_tsep_1(sK4,sK6,sK7)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.73/0.60  fof(f444,plain,(
% 1.73/0.60    ~spl10_12 | spl10_13),
% 1.73/0.60    inference(avatar_split_clause,[],[f436,f442,f438])).
% 1.73/0.60  fof(f436,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f435,f48])).
% 1.73/0.60  fof(f435,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f434,f49])).
% 1.73/0.60  fof(f434,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f433,f50])).
% 1.73/0.60  fof(f433,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f432,f54])).
% 1.73/0.60  fof(f432,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f431,f56])).
% 1.73/0.60  fof(f431,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f430,f57])).
% 1.73/0.60  fof(f430,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f421,f59])).
% 1.73/0.60  fof(f421,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~sP1(X1,sK7,X0,sK6,sK4) | sP0(X1,sK7,sK6,sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK4,sK6,sK7) | ~m1_pre_topc(sK7,sK4) | v2_struct_0(sK7) | ~m1_pre_topc(sK6,sK4) | v2_struct_0(sK6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.73/0.60    inference(superposition,[],[f88,f68])).
% 1.73/0.60  fof(f88,plain,(
% 1.73/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~sP1(X1,X3,X4,X2,X0) | sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f42])).
% 1.73/0.60  fof(f42,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((sP0(X1,X3,X2,X0,X4) | ~sP1(X1,X3,X4,X2,X0)) & (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(nnf_transformation,[],[f24])).
% 1.73/0.60  fof(f24,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((sP0(X1,X3,X2,X0,X4) <=> sP1(X1,X3,X4,X2,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(definition_folding,[],[f13,f23,f22])).
% 1.73/0.60  fof(f13,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(flattening,[],[f12])).
% 1.73/0.60  fof(f12,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f4])).
% 1.73/0.60  fof(f4,axiom,(
% 1.73/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 1.73/0.60  fof(f293,plain,(
% 1.73/0.60    ~spl10_8 | spl10_9),
% 1.73/0.60    inference(avatar_split_clause,[],[f284,f290,f286])).
% 1.73/0.60  fof(f284,plain,(
% 1.73/0.60    sK9 = k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~sP2(sK5,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 1.73/0.60    inference(resolution,[],[f225,f120])).
% 1.73/0.60  fof(f120,plain,(
% 1.73/0.60    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9)),
% 1.73/0.60    inference(forward_demodulation,[],[f70,f68])).
% 1.73/0.60  fof(f70,plain,(
% 1.73/0.60    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK7,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK9)),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f225,plain,(
% 1.73/0.60    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9) | sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3) | ~sP2(sK5,sK7,X3,X2,X1)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f224,f92])).
% 1.73/0.60  fof(f92,plain,(
% 1.73/0.60    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP2(X0,X1,X2,X3,X4)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f45])).
% 1.73/0.60  fof(f45,plain,(
% 1.73/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP2(X0,X1,X2,X3,X4))),
% 1.73/0.60    inference(rectify,[],[f44])).
% 1.73/0.61  fof(f44,plain,(
% 1.73/0.61    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP2(X1,X3,X4,X2,X0))),
% 1.73/0.61    inference(nnf_transformation,[],[f25])).
% 1.73/0.61  fof(f224,plain,(
% 1.73/0.61    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3)) | ~sP2(sK5,sK7,X3,X2,X1)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f219,f93])).
% 1.73/0.61  fof(f93,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP2(X0,X1,X2,X3,X4)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f45])).
% 1.73/0.61  fof(f219,plain,(
% 1.73/0.61    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK5,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK7,X3),sK9) | ~v1_funct_2(k3_tmap_1(X1,sK5,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK7,X3)) | ~sP2(sK5,sK7,X3,X2,X1)) )),
% 1.73/0.61    inference(resolution,[],[f203,f94])).
% 1.73/0.61  fof(f94,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP2(X0,X1,X2,X3,X4)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f45])).
% 1.73/0.61  fof(f203,plain,(
% 1.73/0.61    ( ! [X45] : (~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | sK9 = X45 | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9) | ~v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(X45)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f202,f64])).
% 1.73/0.61  fof(f202,plain,(
% 1.73/0.61    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9) | sK9 = X45 | ~v1_funct_1(sK9) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(X45)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f181,f65])).
% 1.73/0.61  fof(f181,plain,(
% 1.73/0.61    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK5),X45,sK9) | sK9 = X45 | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(sK9) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) | ~v1_funct_2(X45,u1_struct_0(sK7),u1_struct_0(sK5)) | ~v1_funct_1(X45)) )),
% 1.73/0.61    inference(resolution,[],[f90,f67])).
% 1.73/0.61  fof(f90,plain,(
% 1.73/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f43])).
% 1.73/0.61  fof(f43,plain,(
% 1.73/0.61    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.73/0.61    inference(nnf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,plain,(
% 1.73/0.61    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.73/0.61    inference(flattening,[],[f16])).
% 1.73/0.61  fof(f16,plain,(
% 1.73/0.61    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.73/0.61    inference(ennf_transformation,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.73/0.61  fof(f245,plain,(
% 1.73/0.61    ~spl10_7 | spl10_6),
% 1.73/0.61    inference(avatar_split_clause,[],[f240,f236,f242])).
% 1.73/0.61  fof(f240,plain,(
% 1.73/0.61    sK8 = k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)) | ~sP2(sK5,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK4)),
% 1.73/0.61    inference(resolution,[],[f212,f119])).
% 1.73/0.61  fof(f119,plain,(
% 1.73/0.61    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,sK4,sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8)),
% 1.73/0.61    inference(forward_demodulation,[],[f69,f68])).
% 1.73/0.61  fof(f69,plain,(
% 1.73/0.61    r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(sK4,sK5,k1_tsep_1(sK4,sK6,sK7),sK6,k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9)),sK8)),
% 1.73/0.61    inference(cnf_transformation,[],[f35])).
% 1.73/0.61  fof(f212,plain,(
% 1.73/0.61    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8) | sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3) | ~sP2(sK5,sK6,X3,X2,X1)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f211,f92])).
% 1.73/0.61  fof(f211,plain,(
% 1.73/0.61    ( ! [X2,X3,X1] : (sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3)) | ~sP2(sK5,sK6,X3,X2,X1)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f206,f93])).
% 1.73/0.61  fof(f206,plain,(
% 1.73/0.61    ( ! [X2,X3,X1] : (sK8 = k3_tmap_1(X1,sK5,X2,sK6,X3) | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),k3_tmap_1(X1,sK5,X2,sK6,X3),sK8) | ~v1_funct_2(k3_tmap_1(X1,sK5,X2,sK6,X3),u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(k3_tmap_1(X1,sK5,X2,sK6,X3)) | ~sP2(sK5,sK6,X3,X2,X1)) )),
% 1.73/0.61    inference(resolution,[],[f201,f94])).
% 1.73/0.61  fof(f201,plain,(
% 1.73/0.61    ( ! [X44] : (~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | sK8 = X44 | ~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8) | ~v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X44)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f200,f60])).
% 1.73/0.61  fof(f200,plain,(
% 1.73/0.61    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8) | sK8 = X44 | ~v1_funct_1(sK8) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X44)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f180,f61])).
% 1.73/0.61  fof(f180,plain,(
% 1.73/0.61    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK5),X44,sK8) | sK8 = X44 | ~v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(sK8) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK5)))) | ~v1_funct_2(X44,u1_struct_0(sK6),u1_struct_0(sK5)) | ~v1_funct_1(X44)) )),
% 1.73/0.61    inference(resolution,[],[f90,f63])).
% 1.73/0.61  fof(f118,plain,(
% 1.73/0.61    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 1.73/0.61    inference(avatar_split_clause,[],[f71,f115,f111,f107,f103])).
% 1.73/0.61  fof(f71,plain,(
% 1.73/0.61    ~m1_subset_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) | ~v5_pre_topc(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),sK4,sK5) | ~v1_funct_2(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9),u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(k10_tmap_1(sK4,sK5,sK6,sK7,sK8,sK9))),
% 1.73/0.61    inference(cnf_transformation,[],[f35])).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (31180)------------------------------
% 1.73/0.61  % (31180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (31180)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (31180)Memory used [KB]: 7036
% 1.73/0.61  % (31180)Time elapsed: 0.149 s
% 1.73/0.61  % (31180)------------------------------
% 1.73/0.61  % (31180)------------------------------
% 1.88/0.61  % (31175)Success in time 0.244 s
%------------------------------------------------------------------------------

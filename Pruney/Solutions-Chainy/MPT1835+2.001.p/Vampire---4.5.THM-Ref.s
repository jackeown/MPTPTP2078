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
% DateTime   : Thu Dec  3 13:19:51 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  233 (1461 expanded)
%              Number of leaves         :   29 ( 731 expanded)
%              Depth                    :   25
%              Number of atoms          : 1669 (35527 expanded)
%              Number of equality atoms :   38 (1276 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f164,f169,f350,f364,f611,f618,f625,f649,f659,f821,f832,f836])).

fof(f836,plain,
    ( spl11_4
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f833,f614])).

fof(f614,plain,
    ( sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl11_13
  <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f833,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_4 ),
    inference(resolution,[],[f120,f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f101,f60])).

fof(f60,plain,(
    sK5 = k1_tsep_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
      | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
      | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) )
    & r4_tsep_1(sK5,sK7,sK8)
    & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)
    & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    & v5_pre_topc(sK10,sK8,sK6)
    & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    & v5_pre_topc(sK9,sK7,sK6)
    & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    & v1_funct_1(sK9)
    & sK5 = k1_tsep_1(sK5,sK7,sK8)
    & m1_pre_topc(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
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
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK5,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK5 = k1_tsep_1(sK5,X2,X3)
                  & m1_pre_topc(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
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
                        & r4_tsep_1(sK5,X2,X3)
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK5 = k1_tsep_1(sK5,X2,X3)
                & m1_pre_topc(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
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
                      & r4_tsep_1(sK5,X2,X3)
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                      & v5_pre_topc(X5,X3,sK6)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                  & v5_pre_topc(X4,X2,sK6)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6))
                  & v1_funct_1(X4) )
              & sK5 = k1_tsep_1(sK5,X2,X3)
              & m1_pre_topc(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
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
                    & r4_tsep_1(sK5,X2,X3)
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                    & v5_pre_topc(X5,X3,sK6)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                & v5_pre_topc(X4,X2,sK6)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6))
                & v1_funct_1(X4) )
            & sK5 = k1_tsep_1(sK5,X2,X3)
            & m1_pre_topc(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                    | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6)
                    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)) )
                  & r4_tsep_1(sK5,sK7,X3)
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                  & v5_pre_topc(X5,X3,sK6)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
              & v5_pre_topc(X4,sK7,sK6)
              & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
              & v1_funct_1(X4) )
          & sK5 = k1_tsep_1(sK5,sK7,X3)
          & m1_pre_topc(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
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
                & r4_tsep_1(sK5,sK7,X3)
                & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                & v5_pre_topc(X5,X3,sK6)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
            & v5_pre_topc(X4,sK7,sK6)
            & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
            & v1_funct_1(X4) )
        & sK5 = k1_tsep_1(sK5,sK7,X3)
        & m1_pre_topc(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6)
                | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
                | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)) )
              & r4_tsep_1(sK5,sK7,sK8)
              & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
              & v5_pre_topc(X5,sK8,sK6)
              & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
          & v5_pre_topc(X4,sK7,sK6)
          & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6))
          & v1_funct_1(X4) )
      & sK5 = k1_tsep_1(sK5,sK7,sK8)
      & m1_pre_topc(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
              | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6)
              | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6))
              | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)) )
            & r4_tsep_1(sK5,sK7,sK8)
            & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5)
            & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4)
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
          & r4_tsep_1(sK5,sK7,sK8)
          & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5)
          & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9)
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
        & r4_tsep_1(sK5,sK7,sK8)
        & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5)
        & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        & v5_pre_topc(X5,sK8,sK6)
        & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) )
      & r4_tsep_1(sK5,sK7,sK8)
      & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)
      & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( k1_tsep_1(X0,X2,X3) = X0
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
                                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
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
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X2,X3) = X0
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
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).

fof(f101,plain,(
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

fof(f120,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl11_4
  <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f832,plain,
    ( spl11_3
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f828,f613,f298,f114])).

fof(f114,plain,
    ( spl11_3
  <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f298,plain,
    ( spl11_8
  <=> sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f828,plain,
    ( v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(resolution,[],[f826,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK8,sK7,sK5,X0)
      | v5_pre_topc(X0,sK5,X1) ) ),
    inference(superposition,[],[f84,f60])).

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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f826,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f825,f614])).

fof(f825,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f824,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f824,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f823,f54])).

fof(f54,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f823,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f822,f55])).

fof(f55,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f822,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8 ),
    inference(resolution,[],[f299,f452])).

fof(f452,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
      | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f451,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f451,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
      | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f446,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f100,f60])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f446,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
      | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(resolution,[],[f439,f191])).

fof(f439,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f438,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f438,plain,(
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
    inference(subsumption_resolution,[],[f437,f51])).

fof(f51,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f437,plain,(
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
    inference(subsumption_resolution,[],[f436,f52])).

fof(f52,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f436,plain,(
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
    inference(subsumption_resolution,[],[f435,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f435,plain,(
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
    inference(subsumption_resolution,[],[f434,f57])).

fof(f57,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f433,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f432,f59])).

fof(f59,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f432,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK8,sK5)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f423,f71])).

fof(f71,plain,(
    r4_tsep_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | ~ m1_pre_topc(sK8,sK5)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(superposition,[],[f88,f60])).

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

fof(f299,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f298])).

fof(f821,plain,
    ( spl11_8
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f820,f361,f302,f298])).

fof(f302,plain,
    ( spl11_9
  <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f361,plain,
    ( spl11_12
  <=> sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f820,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f819,f61])).

fof(f61,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f819,plain,
    ( ~ v1_funct_1(sK9)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f818,f304])).

fof(f304,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f302])).

fof(f818,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f817,f62])).

fof(f62,plain,(
    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f35])).

fof(f817,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f816,f304])).

fof(f816,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f815,f63])).

fof(f63,plain,(
    v5_pre_topc(sK9,sK7,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f815,plain,
    ( ~ v5_pre_topc(sK9,sK7,sK6)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f814,f304])).

fof(f814,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f813,f64])).

fof(f64,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f813,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f802,f304])).

fof(f802,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f801,f65])).

fof(f65,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f35])).

fof(f801,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f800,f66])).

fof(f66,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f35])).

fof(f800,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f799,f67])).

fof(f67,plain,(
    v5_pre_topc(sK10,sK8,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f799,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v5_pre_topc(sK10,sK8,sK6)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f796,f68])).

fof(f68,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f796,plain,
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
    inference(superposition,[],[f552,f363])).

fof(f363,plain,
    ( sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f361])).

fof(f552,plain,(
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
    inference(superposition,[],[f81,f60])).

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
    inference(nnf_transformation,[],[f21])).

fof(f659,plain,
    ( ~ spl11_7
    | spl11_11
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | ~ spl11_7
    | spl11_11
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f657,f614])).

fof(f657,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f656,f50])).

fof(f656,plain,
    ( v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f655,f51])).

fof(f655,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f654,f52])).

fof(f654,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f653,f53])).

fof(f653,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f652,f54])).

fof(f652,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
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
    | spl11_11 ),
    inference(subsumption_resolution,[],[f650,f168])).

fof(f168,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl11_7
  <=> m1_pre_topc(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f650,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_11 ),
    inference(subsumption_resolution,[],[f639,f59])).

fof(f639,plain,
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
    inference(resolution,[],[f322,f359])).

fof(f359,plain,
    ( ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl11_11
  <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f322,plain,(
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
    inference(subsumption_resolution,[],[f321,f99])).

fof(f321,plain,(
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
    inference(subsumption_resolution,[],[f308,f189])).

fof(f308,plain,(
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
    inference(resolution,[],[f98,f191])).

fof(f98,plain,(
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

fof(f649,plain,
    ( ~ spl11_7
    | spl11_10
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl11_7
    | spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f647,f614])).

fof(f647,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f646,f50])).

fof(f646,plain,
    ( v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f645,f51])).

fof(f645,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f644,f52])).

fof(f644,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f643,f53])).

fof(f643,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f642,f54])).

fof(f642,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f641,f55])).

fof(f641,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f640,f168])).

fof(f640,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_10 ),
    inference(subsumption_resolution,[],[f638,f57])).

fof(f638,plain,
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
    inference(resolution,[],[f322,f349])).

fof(f349,plain,
    ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl11_10
  <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f625,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | spl11_13 ),
    inference(subsumption_resolution,[],[f623,f50])).

fof(f623,plain,
    ( v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f622,f51])).

fof(f622,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f621,f52])).

fof(f621,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f620,f57])).

fof(f620,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f619,f59])).

fof(f619,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(resolution,[],[f615,f579])).

fof(f579,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f578,f56])).

fof(f578,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f577,f61])).

fof(f577,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ v1_funct_1(sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f564,f62])).

fof(f564,plain,(
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
    inference(resolution,[],[f501,f64])).

fof(f501,plain,(
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
    inference(subsumption_resolution,[],[f500,f53])).

fof(f500,plain,(
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
    inference(subsumption_resolution,[],[f499,f54])).

fof(f499,plain,(
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
    inference(subsumption_resolution,[],[f498,f55])).

fof(f498,plain,(
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
    inference(subsumption_resolution,[],[f497,f58])).

fof(f497,plain,(
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
    inference(subsumption_resolution,[],[f496,f65])).

fof(f496,plain,(
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
    inference(subsumption_resolution,[],[f467,f66])).

fof(f467,plain,(
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
    inference(resolution,[],[f102,f68])).

fof(f102,plain,(
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

fof(f615,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f613])).

fof(f618,plain,
    ( ~ spl11_13
    | spl11_2 ),
    inference(avatar_split_clause,[],[f617,f110,f613])).

fof(f110,plain,
    ( spl11_2
  <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f617,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_2 ),
    inference(resolution,[],[f112,f189])).

fof(f112,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f611,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f609,f50])).

fof(f609,plain,
    ( v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f608,f51])).

fof(f608,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f607,f52])).

fof(f607,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f606,f57])).

fof(f606,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f605,f59])).

fof(f605,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(resolution,[],[f579,f138])).

fof(f138,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_1 ),
    inference(resolution,[],[f99,f108])).

fof(f108,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl11_1
  <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f364,plain,
    ( ~ spl11_11
    | spl11_12 ),
    inference(avatar_split_clause,[],[f355,f361,f357])).

fof(f355,plain,
    ( sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    inference(resolution,[],[f270,f123])).

fof(f123,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(forward_demodulation,[],[f70,f60])).

fof(f70,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(cnf_transformation,[],[f35])).

fof(f270,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f269,f95])).

fof(f95,plain,(
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

fof(f269,plain,(
    ! [X2,X3,X1] :
      ( sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3))
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f264,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f264,plain,(
    ! [X2,X3,X1] :
      ( sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | ~ v1_funct_2(k3_tmap_1(X1,sK6,X2,sK8,X3),u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3))
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(resolution,[],[f232,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f232,plain,(
    ! [X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | sK10 = X45
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f231,f65])).

fof(f231,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | sK10 = X45
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f210,f66])).

fof(f210,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | sK10 = X45
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(resolution,[],[f93,f68])).

fof(f93,plain,(
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

fof(f350,plain,
    ( ~ spl11_10
    | spl11_9 ),
    inference(avatar_split_clause,[],[f345,f302,f347])).

fof(f345,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    inference(resolution,[],[f257,f122])).

fof(f122,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(forward_demodulation,[],[f69,f60])).

fof(f69,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f257,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f256,f95])).

fof(f256,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3))
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f251,f96])).

fof(f251,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | ~ v1_funct_2(k3_tmap_1(X1,sK6,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3))
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(resolution,[],[f230,f97])).

fof(f230,plain,(
    ! [X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | sK9 = X44
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f229,f61])).

fof(f229,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | sK9 = X44
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f209,f62])).

fof(f209,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | sK9 = X44
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(resolution,[],[f93,f64])).

fof(f169,plain,
    ( ~ spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f135,f166,f127])).

fof(f127,plain,
    ( spl11_5
  <=> sP2(sK5,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f135,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ sP2(sK5,sK8,sK7) ),
    inference(superposition,[],[f91,f60])).

fof(f91,plain,(
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

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f164,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl11_5 ),
    inference(subsumption_resolution,[],[f162,f50])).

fof(f162,plain,
    ( v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f161,f52])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f160,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f159,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f158,f58])).

fof(f158,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f157,f59])).

fof(f157,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(resolution,[],[f92,f129])).

fof(f129,plain,
    ( ~ sP2(sK5,sK8,sK7)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f92,plain,(
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

fof(f121,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f72,f118,f114,f110,f106])).

fof(f72,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (30931)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.46  % (30920)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.48  % (30917)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.49  % (30910)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (30914)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (30932)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (30915)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (30924)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (30916)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (30929)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (30913)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (30922)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (30923)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (30912)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (30918)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (30919)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (30934)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (30926)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (30928)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (30911)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30930)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (30935)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (30916)Refutation not found, incomplete strategy% (30916)------------------------------
% 0.20/0.53  % (30916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30916)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30916)Memory used [KB]: 11001
% 0.20/0.53  % (30916)Time elapsed: 0.086 s
% 0.20/0.53  % (30916)------------------------------
% 0.20/0.53  % (30916)------------------------------
% 0.20/0.54  % (30927)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (30925)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (30921)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.55  % (30933)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.63/0.57  % (30914)Refutation found. Thanks to Tanya!
% 1.63/0.57  % SZS status Theorem for theBenchmark
% 1.63/0.57  % SZS output start Proof for theBenchmark
% 1.63/0.57  fof(f839,plain,(
% 1.63/0.57    $false),
% 1.63/0.57    inference(avatar_sat_refutation,[],[f121,f164,f169,f350,f364,f611,f618,f625,f649,f659,f821,f832,f836])).
% 1.63/0.57  fof(f836,plain,(
% 1.63/0.57    spl11_4 | ~spl11_13),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f835])).
% 1.63/0.57  fof(f835,plain,(
% 1.63/0.57    $false | (spl11_4 | ~spl11_13)),
% 1.63/0.57    inference(subsumption_resolution,[],[f833,f614])).
% 1.63/0.57  fof(f614,plain,(
% 1.63/0.57    sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_13),
% 1.63/0.57    inference(avatar_component_clause,[],[f613])).
% 1.63/0.57  fof(f613,plain,(
% 1.63/0.57    spl11_13 <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.63/0.57  fof(f833,plain,(
% 1.63/0.57    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_4),
% 1.63/0.57    inference(resolution,[],[f120,f191])).
% 1.63/0.57  fof(f191,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.63/0.57    inference(superposition,[],[f101,f60])).
% 1.63/0.57  fof(f60,plain,(
% 1.63/0.57    sK5 = k1_tsep_1(sK5,sK7,sK8)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f35,plain,(
% 1.63/0.57    ((((((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) & r4_tsep_1(sK5,sK7,sK8) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(sK10,sK8,sK6) & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(sK9,sK7,sK6) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(sK9)) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f9,f34,f33,f32,f31,f30,f29])).
% 1.63/0.57  fof(f29,plain,(
% 1.63/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1) | ~v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5))) & r4_tsep_1(sK5,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f30,plain,(
% 1.63/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1) | ~v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5))) & r4_tsep_1(sK5,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5))) & r4_tsep_1(sK5,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6)))) & v5_pre_topc(X4,X2,sK6) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f31,plain,(
% 1.63/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5))) & r4_tsep_1(sK5,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6)))) & v5_pre_topc(X4,X2,sK6) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5))) & r4_tsep_1(sK5,sK7,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,sK7,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f32,plain,(
% 1.63/0.57    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5))) & r4_tsep_1(sK5,sK7,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,sK7,X3) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5))) & r4_tsep_1(sK5,sK7,sK8) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f33,plain,(
% 1.63/0.57    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5))) & r4_tsep_1(sK5,sK7,sK8) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5))) & r4_tsep_1(sK5,sK7,sK8) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(sK9,sK7,sK6) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(sK9))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f34,plain,(
% 1.63/0.57    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5))) & r4_tsep_1(sK5,sK7,sK8) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) & r4_tsep_1(sK5,sK7,sK8) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(sK10,sK8,sK6) & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(sK10))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f9,plain,(
% 1.63/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.63/0.57    inference(flattening,[],[f8])).
% 1.63/0.57  fof(f8,plain,(
% 1.63/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f7])).
% 1.63/0.57  fof(f7,negated_conjecture,(
% 1.63/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 1.63/0.57    inference(negated_conjecture,[],[f6])).
% 1.63/0.57  fof(f6,conjecture,(
% 1.63/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).
% 1.63/0.57  fof(f101,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f49])).
% 1.63/0.57  fof(f49,plain,(
% 1.63/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP4(X0,X1,X2,X3,X4,X5))),
% 1.63/0.57    inference(rectify,[],[f48])).
% 1.63/0.57  fof(f48,plain,(
% 1.63/0.57    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP4(X1,X3,X2,X0,X5,X4))),
% 1.63/0.57    inference(nnf_transformation,[],[f27])).
% 1.63/0.57  fof(f27,plain,(
% 1.63/0.57    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP4(X1,X3,X2,X0,X5,X4))),
% 1.63/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.63/0.57  fof(f120,plain,(
% 1.63/0.57    ~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | spl11_4),
% 1.63/0.57    inference(avatar_component_clause,[],[f118])).
% 1.63/0.57  fof(f118,plain,(
% 1.63/0.57    spl11_4 <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.63/0.57  fof(f832,plain,(
% 1.63/0.57    spl11_3 | ~spl11_8 | ~spl11_13),
% 1.63/0.57    inference(avatar_split_clause,[],[f828,f613,f298,f114])).
% 1.63/0.57  fof(f114,plain,(
% 1.63/0.57    spl11_3 <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.63/0.57  fof(f298,plain,(
% 1.63/0.57    spl11_8 <=> sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.63/0.57  fof(f828,plain,(
% 1.63/0.57    v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | (~spl11_8 | ~spl11_13)),
% 1.63/0.57    inference(resolution,[],[f826,f136])).
% 1.63/0.57  fof(f136,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~sP0(X1,sK8,sK7,sK5,X0) | v5_pre_topc(X0,sK5,X1)) )),
% 1.63/0.57    inference(superposition,[],[f84,f60])).
% 1.63/0.57  fof(f84,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f41])).
% 1.63/0.57  fof(f41,plain,(
% 1.63/0.57    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.63/0.57    inference(rectify,[],[f40])).
% 1.63/0.57  fof(f40,plain,(
% 1.63/0.57    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.63/0.57    inference(flattening,[],[f39])).
% 1.63/0.57  fof(f39,plain,(
% 1.63/0.57    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.63/0.57    inference(nnf_transformation,[],[f20])).
% 1.63/0.57  fof(f20,plain,(
% 1.63/0.57    ! [X1,X3,X2,X0,X4] : (sP0(X1,X3,X2,X0,X4) <=> (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))),
% 1.63/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.63/0.57  fof(f826,plain,(
% 1.63/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | (~spl11_8 | ~spl11_13)),
% 1.63/0.57    inference(subsumption_resolution,[],[f825,f614])).
% 1.63/0.57  fof(f825,plain,(
% 1.63/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.63/0.57    inference(subsumption_resolution,[],[f824,f53])).
% 1.63/0.57  fof(f53,plain,(
% 1.63/0.57    ~v2_struct_0(sK6)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f824,plain,(
% 1.63/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.63/0.57    inference(subsumption_resolution,[],[f823,f54])).
% 1.63/0.57  fof(f54,plain,(
% 1.63/0.57    v2_pre_topc(sK6)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f823,plain,(
% 1.63/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.63/0.57    inference(subsumption_resolution,[],[f822,f55])).
% 1.63/0.57  fof(f55,plain,(
% 1.63/0.57    l1_pre_topc(sK6)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f822,plain,(
% 1.63/0.57    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_8),
% 1.63/0.57    inference(resolution,[],[f299,f452])).
% 1.63/0.57  fof(f452,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f451,f99])).
% 1.63/0.57  fof(f99,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f49])).
% 1.63/0.57  fof(f451,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f446,f189])).
% 1.63/0.57  fof(f189,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.63/0.57    inference(superposition,[],[f100,f60])).
% 1.63/0.57  fof(f100,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f49])).
% 1.63/0.57  fof(f446,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.63/0.57    inference(resolution,[],[f439,f191])).
% 1.63/0.57  fof(f439,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f438,f50])).
% 1.63/0.57  fof(f50,plain,(
% 1.63/0.57    ~v2_struct_0(sK5)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f438,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f437,f51])).
% 1.63/0.57  fof(f51,plain,(
% 1.63/0.57    v2_pre_topc(sK5)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f437,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f436,f52])).
% 1.63/0.57  fof(f52,plain,(
% 1.63/0.57    l1_pre_topc(sK5)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f436,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f435,f56])).
% 1.63/0.57  fof(f56,plain,(
% 1.63/0.57    ~v2_struct_0(sK7)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f435,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f434,f57])).
% 1.63/0.57  fof(f57,plain,(
% 1.63/0.57    m1_pre_topc(sK7,sK5)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f434,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f433,f58])).
% 1.63/0.57  fof(f58,plain,(
% 1.63/0.57    ~v2_struct_0(sK8)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f433,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f432,f59])).
% 1.63/0.57  fof(f59,plain,(
% 1.63/0.57    m1_pre_topc(sK8,sK5)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f432,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f423,f71])).
% 1.63/0.57  fof(f71,plain,(
% 1.63/0.57    r4_tsep_1(sK5,sK7,sK8)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f423,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~m1_pre_topc(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.63/0.57    inference(superposition,[],[f88,f60])).
% 1.63/0.57  fof(f88,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~sP1(X1,X3,X4,X2,X0) | sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f42])).
% 1.63/0.57  fof(f42,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((sP0(X1,X3,X2,X0,X4) | ~sP1(X1,X3,X4,X2,X0)) & (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.57    inference(nnf_transformation,[],[f22])).
% 1.63/0.57  fof(f22,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((sP0(X1,X3,X2,X0,X4) <=> sP1(X1,X3,X4,X2,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.57    inference(definition_folding,[],[f11,f21,f20])).
% 1.63/0.57  fof(f21,plain,(
% 1.63/0.57    ! [X1,X3,X4,X2,X0] : (sP1(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 1.63/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.63/0.57  fof(f11,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.57    inference(flattening,[],[f10])).
% 1.63/0.57  fof(f10,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f5])).
% 1.63/0.57  fof(f5,axiom,(
% 1.63/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 1.63/0.57  fof(f299,plain,(
% 1.63/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~spl11_8),
% 1.63/0.57    inference(avatar_component_clause,[],[f298])).
% 1.63/0.57  fof(f821,plain,(
% 1.63/0.57    spl11_8 | ~spl11_9 | ~spl11_12),
% 1.63/0.57    inference(avatar_split_clause,[],[f820,f361,f302,f298])).
% 1.63/0.57  fof(f302,plain,(
% 1.63/0.57    spl11_9 <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.63/0.57  fof(f361,plain,(
% 1.63/0.57    spl11_12 <=> sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.63/0.57  fof(f820,plain,(
% 1.63/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(subsumption_resolution,[],[f819,f61])).
% 1.63/0.57  fof(f61,plain,(
% 1.63/0.57    v1_funct_1(sK9)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f819,plain,(
% 1.63/0.57    ~v1_funct_1(sK9) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(forward_demodulation,[],[f818,f304])).
% 1.63/0.57  fof(f304,plain,(
% 1.63/0.57    sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~spl11_9),
% 1.63/0.57    inference(avatar_component_clause,[],[f302])).
% 1.63/0.57  fof(f818,plain,(
% 1.63/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(subsumption_resolution,[],[f817,f62])).
% 1.63/0.57  fof(f62,plain,(
% 1.63/0.57    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f817,plain,(
% 1.63/0.57    ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(forward_demodulation,[],[f816,f304])).
% 1.63/0.57  fof(f816,plain,(
% 1.63/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(subsumption_resolution,[],[f815,f63])).
% 1.63/0.57  fof(f63,plain,(
% 1.63/0.57    v5_pre_topc(sK9,sK7,sK6)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f815,plain,(
% 1.63/0.57    ~v5_pre_topc(sK9,sK7,sK6) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(forward_demodulation,[],[f814,f304])).
% 1.63/0.57  fof(f814,plain,(
% 1.63/0.57    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(subsumption_resolution,[],[f813,f64])).
% 1.63/0.57  fof(f64,plain,(
% 1.63/0.57    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f813,plain,(
% 1.63/0.57    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.63/0.57    inference(forward_demodulation,[],[f802,f304])).
% 1.63/0.57  fof(f802,plain,(
% 1.63/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.63/0.57    inference(subsumption_resolution,[],[f801,f65])).
% 1.63/0.57  fof(f65,plain,(
% 1.63/0.57    v1_funct_1(sK10)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f801,plain,(
% 1.63/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.63/0.57    inference(subsumption_resolution,[],[f800,f66])).
% 1.63/0.57  fof(f66,plain,(
% 1.63/0.57    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f800,plain,(
% 1.63/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.63/0.57    inference(subsumption_resolution,[],[f799,f67])).
% 1.63/0.57  fof(f67,plain,(
% 1.63/0.57    v5_pre_topc(sK10,sK8,sK6)),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f799,plain,(
% 1.63/0.57    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v5_pre_topc(sK10,sK8,sK6) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.63/0.57    inference(subsumption_resolution,[],[f796,f68])).
% 1.63/0.57  fof(f68,plain,(
% 1.63/0.57    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))),
% 1.63/0.57    inference(cnf_transformation,[],[f35])).
% 1.63/0.57  fof(f796,plain,(
% 1.63/0.57    ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v5_pre_topc(sK10,sK8,sK6) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.63/0.57    inference(superposition,[],[f552,f363])).
% 1.63/0.57  fof(f363,plain,(
% 1.63/0.57    sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~spl11_12),
% 1.63/0.57    inference(avatar_component_clause,[],[f361])).
% 1.63/0.57  fof(f552,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK8,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK8,X1),sK8,X0) | ~v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK8,X1),u1_struct_0(sK8),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK8,X1)) | sP1(X0,sK8,X1,sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK7,X1),sK7,X0) | ~v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK7,X1))) )),
% 1.63/0.57    inference(superposition,[],[f81,f60])).
% 1.63/0.57  fof(f81,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP1(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f38])).
% 1.63/0.57  fof(f38,plain,(
% 1.63/0.57    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.63/0.57    inference(rectify,[],[f37])).
% 1.63/0.57  fof(f37,plain,(
% 1.63/0.57    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.63/0.57    inference(flattening,[],[f36])).
% 1.63/0.57  fof(f36,plain,(
% 1.63/0.57    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.63/0.57    inference(nnf_transformation,[],[f21])).
% 1.63/0.57  fof(f659,plain,(
% 1.63/0.57    ~spl11_7 | spl11_11 | ~spl11_13),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f658])).
% 1.63/0.57  fof(f658,plain,(
% 1.63/0.57    $false | (~spl11_7 | spl11_11 | ~spl11_13)),
% 1.63/0.57    inference(subsumption_resolution,[],[f657,f614])).
% 1.63/0.58  fof(f657,plain,(
% 1.63/0.58    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f656,f50])).
% 1.63/0.58  fof(f656,plain,(
% 1.63/0.58    v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f655,f51])).
% 1.63/0.58  fof(f655,plain,(
% 1.63/0.58    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f654,f52])).
% 1.63/0.58  fof(f654,plain,(
% 1.63/0.58    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f653,f53])).
% 1.63/0.58  fof(f653,plain,(
% 1.63/0.58    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f652,f54])).
% 1.63/0.58  fof(f652,plain,(
% 1.63/0.58    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f651,f55])).
% 1.63/0.58  fof(f651,plain,(
% 1.63/0.58    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.63/0.58    inference(subsumption_resolution,[],[f650,f168])).
% 1.63/0.58  fof(f168,plain,(
% 1.63/0.58    m1_pre_topc(sK5,sK5) | ~spl11_7),
% 1.63/0.58    inference(avatar_component_clause,[],[f166])).
% 1.63/0.58  fof(f166,plain,(
% 1.63/0.58    spl11_7 <=> m1_pre_topc(sK5,sK5)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.63/0.58  fof(f650,plain,(
% 1.63/0.58    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_11),
% 1.63/0.58    inference(subsumption_resolution,[],[f639,f59])).
% 1.63/0.58  fof(f639,plain,(
% 1.63/0.58    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_11),
% 1.63/0.58    inference(resolution,[],[f322,f359])).
% 1.63/0.58  fof(f359,plain,(
% 1.63/0.58    ~sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) | spl11_11),
% 1.63/0.58    inference(avatar_component_clause,[],[f357])).
% 1.63/0.58  fof(f357,plain,(
% 1.63/0.58    spl11_11 <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.63/0.58  fof(f322,plain,(
% 1.63/0.58    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f321,f99])).
% 1.63/0.58  fof(f321,plain,(
% 1.63/0.58    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f308,f189])).
% 1.63/0.58  fof(f308,plain,(
% 1.63/0.58    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~v1_funct_2(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),u1_struct_0(sK5),u1_struct_0(X8)) | ~v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.63/0.58    inference(resolution,[],[f98,f191])).
% 1.63/0.58  fof(f98,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP3(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : (sP3(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(definition_folding,[],[f17,f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP3(X1,X3,X4,X2,X0))),
% 1.63/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(flattening,[],[f16])).
% 1.63/0.58  fof(f16,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f4])).
% 1.63/0.58  fof(f4,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.63/0.58  fof(f649,plain,(
% 1.63/0.58    ~spl11_7 | spl11_10 | ~spl11_13),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f648])).
% 1.63/0.58  fof(f648,plain,(
% 1.63/0.58    $false | (~spl11_7 | spl11_10 | ~spl11_13)),
% 1.63/0.58    inference(subsumption_resolution,[],[f647,f614])).
% 1.63/0.58  fof(f647,plain,(
% 1.63/0.58    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f646,f50])).
% 1.63/0.58  fof(f646,plain,(
% 1.63/0.58    v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f645,f51])).
% 1.63/0.58  fof(f645,plain,(
% 1.63/0.58    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f644,f52])).
% 1.63/0.58  fof(f644,plain,(
% 1.63/0.58    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f643,f53])).
% 1.63/0.58  fof(f643,plain,(
% 1.63/0.58    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f642,f54])).
% 1.63/0.58  fof(f642,plain,(
% 1.63/0.58    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f641,f55])).
% 1.63/0.58  fof(f641,plain,(
% 1.63/0.58    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f640,f168])).
% 1.63/0.58  fof(f640,plain,(
% 1.63/0.58    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_10),
% 1.63/0.58    inference(subsumption_resolution,[],[f638,f57])).
% 1.63/0.58  fof(f638,plain,(
% 1.63/0.58    ~m1_pre_topc(sK7,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_10),
% 1.63/0.58    inference(resolution,[],[f322,f349])).
% 1.63/0.58  fof(f349,plain,(
% 1.63/0.58    ~sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) | spl11_10),
% 1.63/0.58    inference(avatar_component_clause,[],[f347])).
% 1.63/0.58  fof(f347,plain,(
% 1.63/0.58    spl11_10 <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.63/0.58  fof(f625,plain,(
% 1.63/0.58    spl11_13),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f624])).
% 1.63/0.58  fof(f624,plain,(
% 1.63/0.58    $false | spl11_13),
% 1.63/0.58    inference(subsumption_resolution,[],[f623,f50])).
% 1.63/0.58  fof(f623,plain,(
% 1.63/0.58    v2_struct_0(sK5) | spl11_13),
% 1.63/0.58    inference(subsumption_resolution,[],[f622,f51])).
% 1.63/0.58  fof(f622,plain,(
% 1.63/0.58    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.63/0.58    inference(subsumption_resolution,[],[f621,f52])).
% 1.63/0.58  fof(f621,plain,(
% 1.63/0.58    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.63/0.58    inference(subsumption_resolution,[],[f620,f57])).
% 1.63/0.58  fof(f620,plain,(
% 1.63/0.58    ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.63/0.58    inference(subsumption_resolution,[],[f619,f59])).
% 1.63/0.58  fof(f619,plain,(
% 1.63/0.58    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.63/0.58    inference(resolution,[],[f615,f579])).
% 1.63/0.58  fof(f579,plain,(
% 1.63/0.58    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f578,f56])).
% 1.63/0.58  fof(f578,plain,(
% 1.63/0.58    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f577,f61])).
% 1.63/0.58  fof(f577,plain,(
% 1.63/0.58    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~v1_funct_1(sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f564,f62])).
% 1.63/0.58  fof(f564,plain,(
% 1.63/0.58    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(resolution,[],[f501,f64])).
% 1.63/0.58  fof(f501,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f500,f53])).
% 1.63/0.58  fof(f500,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f499,f54])).
% 1.63/0.58  fof(f499,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f498,f55])).
% 1.63/0.58  fof(f498,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f497,f58])).
% 1.63/0.58  fof(f497,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f496,f65])).
% 1.63/0.58  fof(f496,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_1(sK10) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f467,f66])).
% 1.63/0.58  fof(f467,plain,(
% 1.63/0.58    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.63/0.58    inference(resolution,[],[f102,f68])).
% 1.63/0.58  fof(f102,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP4(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f28])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4,X5] : (sP4(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(definition_folding,[],[f19,f27])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(flattening,[],[f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f2])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.63/0.58  fof(f615,plain,(
% 1.63/0.58    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_13),
% 1.63/0.58    inference(avatar_component_clause,[],[f613])).
% 1.63/0.58  fof(f618,plain,(
% 1.63/0.58    ~spl11_13 | spl11_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f617,f110,f613])).
% 1.63/0.58  fof(f110,plain,(
% 1.63/0.58    spl11_2 <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.63/0.58  fof(f617,plain,(
% 1.63/0.58    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_2),
% 1.63/0.58    inference(resolution,[],[f112,f189])).
% 1.63/0.58  fof(f112,plain,(
% 1.63/0.58    ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | spl11_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f110])).
% 1.63/0.58  fof(f611,plain,(
% 1.63/0.58    spl11_1),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f610])).
% 1.63/0.58  fof(f610,plain,(
% 1.63/0.58    $false | spl11_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f609,f50])).
% 1.63/0.58  fof(f609,plain,(
% 1.63/0.58    v2_struct_0(sK5) | spl11_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f608,f51])).
% 1.63/0.58  fof(f608,plain,(
% 1.63/0.58    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f607,f52])).
% 1.63/0.58  fof(f607,plain,(
% 1.63/0.58    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f606,f57])).
% 1.63/0.58  fof(f606,plain,(
% 1.63/0.58    ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f605,f59])).
% 1.63/0.58  fof(f605,plain,(
% 1.63/0.58    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.63/0.58    inference(resolution,[],[f579,f138])).
% 1.63/0.58  fof(f138,plain,(
% 1.63/0.58    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_1),
% 1.63/0.58    inference(resolution,[],[f99,f108])).
% 1.63/0.58  fof(f108,plain,(
% 1.63/0.58    ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | spl11_1),
% 1.63/0.58    inference(avatar_component_clause,[],[f106])).
% 1.63/0.58  fof(f106,plain,(
% 1.63/0.58    spl11_1 <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.63/0.58  fof(f364,plain,(
% 1.63/0.58    ~spl11_11 | spl11_12),
% 1.63/0.58    inference(avatar_split_clause,[],[f355,f361,f357])).
% 1.63/0.58  fof(f355,plain,(
% 1.63/0.58    sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.63/0.58    inference(resolution,[],[f270,f123])).
% 1.63/0.58  fof(f123,plain,(
% 1.63/0.58    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)),
% 1.63/0.58    inference(forward_demodulation,[],[f70,f60])).
% 1.63/0.58  fof(f70,plain,(
% 1.63/0.58    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)),
% 1.63/0.58    inference(cnf_transformation,[],[f35])).
% 1.63/0.58  fof(f270,plain,(
% 1.63/0.58    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f269,f95])).
% 1.63/0.58  fof(f95,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f47])).
% 1.63/0.58  fof(f47,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP3(X0,X1,X2,X3,X4))),
% 1.63/0.58    inference(rectify,[],[f46])).
% 1.63/0.58  fof(f46,plain,(
% 1.63/0.58    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP3(X1,X3,X4,X2,X0))),
% 1.63/0.58    inference(nnf_transformation,[],[f25])).
% 1.63/0.58  fof(f269,plain,(
% 1.63/0.58    ( ! [X2,X3,X1] : (sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3)) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f264,f96])).
% 1.63/0.58  fof(f96,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f47])).
% 1.63/0.58  fof(f264,plain,(
% 1.63/0.58    ( ! [X2,X3,X1] : (sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | ~v1_funct_2(k3_tmap_1(X1,sK6,X2,sK8,X3),u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3)) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.63/0.58    inference(resolution,[],[f232,f97])).
% 1.63/0.58  fof(f97,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f47])).
% 1.63/0.58  fof(f232,plain,(
% 1.63/0.58    ( ! [X45] : (~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | sK10 = X45 | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f231,f65])).
% 1.63/0.58  fof(f231,plain,(
% 1.63/0.58    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | sK10 = X45 | ~v1_funct_1(sK10) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f210,f66])).
% 1.63/0.58  fof(f210,plain,(
% 1.63/0.58    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | sK10 = X45 | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.63/0.58    inference(resolution,[],[f93,f68])).
% 1.63/0.58  fof(f93,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f45])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.63/0.58    inference(nnf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.63/0.58    inference(flattening,[],[f14])).
% 1.63/0.58  fof(f14,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.63/0.58    inference(ennf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.63/0.58  fof(f350,plain,(
% 1.63/0.58    ~spl11_10 | spl11_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f345,f302,f347])).
% 1.63/0.58  fof(f345,plain,(
% 1.63/0.58    sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.63/0.58    inference(resolution,[],[f257,f122])).
% 1.63/0.58  fof(f122,plain,(
% 1.63/0.58    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)),
% 1.63/0.58    inference(forward_demodulation,[],[f69,f60])).
% 1.63/0.58  fof(f69,plain,(
% 1.63/0.58    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)),
% 1.63/0.58    inference(cnf_transformation,[],[f35])).
% 1.63/0.58  fof(f257,plain,(
% 1.63/0.58    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f256,f95])).
% 1.63/0.58  fof(f256,plain,(
% 1.63/0.58    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3)) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f251,f96])).
% 1.63/0.58  fof(f251,plain,(
% 1.63/0.58    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | ~v1_funct_2(k3_tmap_1(X1,sK6,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3)) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.63/0.58    inference(resolution,[],[f230,f97])).
% 1.63/0.58  fof(f230,plain,(
% 1.63/0.58    ( ! [X44] : (~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sK9 = X44 | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f229,f61])).
% 1.63/0.58  fof(f229,plain,(
% 1.63/0.58    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | sK9 = X44 | ~v1_funct_1(sK9) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f209,f62])).
% 1.63/0.58  fof(f209,plain,(
% 1.63/0.58    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | sK9 = X44 | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(sK9) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.63/0.58    inference(resolution,[],[f93,f64])).
% 1.63/0.58  fof(f169,plain,(
% 1.63/0.58    ~spl11_5 | spl11_7),
% 1.63/0.58    inference(avatar_split_clause,[],[f135,f166,f127])).
% 1.63/0.58  fof(f127,plain,(
% 1.63/0.58    spl11_5 <=> sP2(sK5,sK8,sK7)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.63/0.58  fof(f135,plain,(
% 1.63/0.58    m1_pre_topc(sK5,sK5) | ~sP2(sK5,sK8,sK7)),
% 1.63/0.58    inference(superposition,[],[f91,f60])).
% 1.63/0.58  fof(f91,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP2(X0,X1,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f44])).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP2(X0,X1,X2))),
% 1.63/0.58    inference(rectify,[],[f43])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 1.63/0.58    inference(nnf_transformation,[],[f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 1.63/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.63/0.58  fof(f164,plain,(
% 1.63/0.58    spl11_5),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f163])).
% 1.63/0.58  fof(f163,plain,(
% 1.63/0.58    $false | spl11_5),
% 1.63/0.58    inference(subsumption_resolution,[],[f162,f50])).
% 1.63/0.58  fof(f162,plain,(
% 1.63/0.58    v2_struct_0(sK5) | spl11_5),
% 1.63/0.58    inference(subsumption_resolution,[],[f161,f52])).
% 1.63/0.58  fof(f161,plain,(
% 1.63/0.58    ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.63/0.58    inference(subsumption_resolution,[],[f160,f56])).
% 1.63/0.58  fof(f160,plain,(
% 1.63/0.58    v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.63/0.58    inference(subsumption_resolution,[],[f159,f57])).
% 1.63/0.58  fof(f159,plain,(
% 1.63/0.58    ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.63/0.58    inference(subsumption_resolution,[],[f158,f58])).
% 1.63/0.58  fof(f158,plain,(
% 1.63/0.58    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.63/0.58    inference(subsumption_resolution,[],[f157,f59])).
% 1.63/0.58  fof(f157,plain,(
% 1.63/0.58    ~m1_pre_topc(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.63/0.58    inference(resolution,[],[f92,f129])).
% 1.63/0.58  fof(f129,plain,(
% 1.63/0.58    ~sP2(sK5,sK8,sK7) | spl11_5),
% 1.63/0.58    inference(avatar_component_clause,[],[f127])).
% 1.63/0.58  fof(f92,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(definition_folding,[],[f13,f23])).
% 1.63/0.58  fof(f13,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(flattening,[],[f12])).
% 1.63/0.58  fof(f12,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.63/0.58  fof(f121,plain,(
% 1.63/0.58    ~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f72,f118,f114,f110,f106])).
% 1.63/0.58  fof(f72,plain,(
% 1.63/0.58    ~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.63/0.58    inference(cnf_transformation,[],[f35])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (30914)------------------------------
% 1.63/0.58  % (30914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (30914)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (30914)Memory used [KB]: 7036
% 1.63/0.58  % (30914)Time elapsed: 0.172 s
% 1.63/0.58  % (30914)------------------------------
% 1.63/0.58  % (30914)------------------------------
% 1.63/0.58  % (30909)Success in time 0.219 s
%------------------------------------------------------------------------------

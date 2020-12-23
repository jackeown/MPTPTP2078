%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  320 (3760 expanded)
%              Number of leaves         :   26 (1809 expanded)
%              Depth                    :   27
%              Number of atoms          : 3012 (91236 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f692,f718,f740,f758,f932,f1486,f1595,f1616,f1658,f1738,f1741])).

fof(f1741,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104
    | spl8_106 ),
    inference(avatar_contradiction_clause,[],[f1740])).

fof(f1740,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104
    | spl8_106 ),
    inference(subsumption_resolution,[],[f1739,f62])).

fof(f62,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f34,f33,f32,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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
    inference(pure_predicate_removal,[],[f8])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

fof(f1739,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104
    | spl8_106 ),
    inference(forward_demodulation,[],[f1478,f1685])).

fof(f1685,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104 ),
    inference(subsumption_resolution,[],[f1684,f1329])).

fof(f1329,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1290,f54])).

fof(f54,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f1290,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1289,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f1289,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1288,f52])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f1288,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1287,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f1287,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1286,f54])).

fof(f1286,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1285,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f1285,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1284,f46])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f1284,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1283,f47])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f1283,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f1282])).

fof(f1282,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1012,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f1012,plain,
    ( ! [X10,X11] :
        ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10)
        | ~ m1_pre_topc(X11,X10)
        | v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1011,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1011,plain,
    ( ! [X10,X11] :
        ( v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ m1_pre_topc(X11,X10)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1010,f49])).

fof(f49,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1010,plain,
    ( ! [X10,X11] :
        ( v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ m1_pre_topc(X11,X10)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1009,f50])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1009,plain,
    ( ! [X10,X11] :
        ( v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ m1_pre_topc(X11,X10)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1008,f100])).

fof(f100,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_1
  <=> v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1008,plain,
    ( ! [X10,X11] :
        ( v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
        | ~ m1_pre_topc(X11,X10)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f945,f104])).

fof(f104,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_2
  <=> v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f945,plain,
    ( ! [X10,X11] :
        ( v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
        | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
        | ~ m1_pre_topc(X11,X10)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl8_4 ),
    inference(resolution,[],[f112,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f112,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_4
  <=> m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1684,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104 ),
    inference(subsumption_resolution,[],[f1683,f1469])).

fof(f1469,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f1468,plain,
    ( spl8_104
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f1683,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f1668,f717])).

fof(f717,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f715])).

fof(f715,plain,
    ( spl8_45
  <=> r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f1668,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1437,f176])).

fof(f176,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | sK7 = X10
      | ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X10,sK7)
      | ~ v1_funct_2(X10,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f175,f59])).

fof(f59,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f175,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X10,sK7)
      | sK7 = X10
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v1_funct_2(X10,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f151,f60])).

fof(f60,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f151,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X10,sK7)
      | sK7 = X10
      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v1_funct_2(X10,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(X10) ) ),
    inference(resolution,[],[f62,f86])).

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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f1437,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1325,f54])).

fof(f1325,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1324,f51])).

fof(f1324,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1323,f52])).

fof(f1323,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1322,f53])).

fof(f1322,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1321,f54])).

fof(f1321,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1320,f45])).

fof(f1320,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1319,f46])).

fof(f1319,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1318,f47])).

fof(f1318,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f1317])).

fof(f1317,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1017,f85])).

fof(f1017,plain,
    ( ! [X12,X13] :
        ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12)
        | ~ m1_pre_topc(X13,X12)
        | m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3))))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1016,f48])).

fof(f1016,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3))))
        | ~ m1_pre_topc(X13,X12)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1015,f49])).

fof(f1015,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3))))
        | ~ m1_pre_topc(X13,X12)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1014,f50])).

fof(f1014,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3))))
        | ~ m1_pre_topc(X13,X12)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1013,f100])).

fof(f1013,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3))))
        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
        | ~ m1_pre_topc(X13,X12)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f946,f104])).

fof(f946,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3))))
        | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
        | ~ m1_pre_topc(X13,X12)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) )
    | ~ spl8_4 ),
    inference(resolution,[],[f112,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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

fof(f1478,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_106 ),
    inference(avatar_component_clause,[],[f1476])).

fof(f1476,plain,
    ( spl8_106
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f1738,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104
    | spl8_105 ),
    inference(avatar_contradiction_clause,[],[f1737])).

fof(f1737,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104
    | spl8_105 ),
    inference(subsumption_resolution,[],[f1732,f61])).

fof(f61,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1732,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_45
    | ~ spl8_104
    | spl8_105 ),
    inference(backward_demodulation,[],[f1474,f1685])).

fof(f1474,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | spl8_105 ),
    inference(avatar_component_clause,[],[f1472])).

fof(f1472,plain,
    ( spl8_105
  <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f1658,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(avatar_contradiction_clause,[],[f1657])).

fof(f1657,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1656,f45])).

fof(f1656,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1655,f47])).

fof(f1655,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1654,f51])).

fof(f1654,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1653,f52])).

fof(f1653,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1652,f53])).

fof(f1652,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1651,f54])).

fof(f1651,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(resolution,[],[f1641,f85])).

fof(f1641,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1640,f45])).

fof(f1640,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1639,f46])).

fof(f1639,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1638,f47])).

fof(f1638,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1637,f48])).

fof(f1637,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1636,f49])).

fof(f1636,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1635,f50])).

fof(f1635,plain,
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
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1634,f54])).

fof(f1634,plain,
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
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1633,f100])).

fof(f1633,plain,
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
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1632,f104])).

fof(f1632,plain,
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
    | spl8_104 ),
    inference(subsumption_resolution,[],[f1631,f112])).

fof(f1631,plain,
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
    | spl8_104 ),
    inference(resolution,[],[f1470,f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f1470,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_104 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f1616,plain,
    ( ~ spl8_104
    | ~ spl8_105
    | ~ spl8_106
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(avatar_split_clause,[],[f1615,f1483,f111,f107,f103,f99,f1476,f1472,f1468])).

fof(f107,plain,
    ( spl8_3
  <=> v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1483,plain,
    ( spl8_107
  <=> sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f1615,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1614,f55])).

fof(f55,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f1614,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1613,f56])).

fof(f56,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1613,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1612,f57])).

fof(f57,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1612,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK6,sK4,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1611,f1034])).

fof(f1034,plain,
    ( ~ sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f1032,f109])).

fof(f109,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1032,plain,
    ( ~ sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f961,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f961,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f960,f45])).

fof(f960,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f959,f46])).

fof(f959,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f958,f47])).

fof(f958,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f957,f48])).

fof(f957,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f956,f49])).

fof(f956,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f955,f50])).

fof(f955,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f954,f51])).

fof(f954,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f953,f52])).

fof(f953,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f952,f53])).

fof(f952,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
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
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f951,f54])).

fof(f951,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
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
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f950,f64])).

fof(f64,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f950,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
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
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f949,f100])).

fof(f949,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f937,f104])).

fof(f937,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f112,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | sP1(X0,X2,X4,X3,X1)
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(definition_folding,[],[f15,f27,f26])).

fof(f26,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f1611,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | ~ v5_pre_topc(sK6,sK4,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1610,f1329])).

fof(f1610,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | ~ v5_pre_topc(sK6,sK4,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl8_107 ),
    inference(subsumption_resolution,[],[f1608,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f1608,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | ~ v5_pre_topc(sK6,sK4,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ spl8_107 ),
    inference(superposition,[],[f79,f1485])).

fof(f1485,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_107 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f1595,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(avatar_contradiction_clause,[],[f1594])).

fof(f1594,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1593,f45])).

fof(f1593,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1592,f47])).

fof(f1592,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1591,f51])).

fof(f1591,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1590,f52])).

fof(f1590,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1589,f53])).

fof(f1589,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1588,f54])).

fof(f1588,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(resolution,[],[f1587,f85])).

fof(f1587,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1586,f45])).

fof(f1586,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1585,f46])).

fof(f1585,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1584,f47])).

fof(f1584,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1583,f48])).

fof(f1583,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1582,f49])).

fof(f1582,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1581,f50])).

fof(f1581,plain,
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
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1580,f52])).

fof(f1580,plain,
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
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1579,f100])).

fof(f1579,plain,
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
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1578,f104])).

fof(f1578,plain,
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
    | spl8_102 ),
    inference(subsumption_resolution,[],[f1577,f112])).

fof(f1577,plain,
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
    | spl8_102 ),
    inference(resolution,[],[f1462,f89])).

fof(f1462,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl8_102 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f1460,plain,
    ( spl8_102
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f1486,plain,
    ( ~ spl8_102
    | spl8_107
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f1481,f737,f111,f103,f99,f1483,f1460])).

fof(f737,plain,
    ( spl8_46
  <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f1481,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1480,f1328])).

fof(f1328,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1290,f52])).

fof(f1480,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1441,f739])).

fof(f739,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f737])).

fof(f1441,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1436,f144])).

fof(f144,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | sK6 = X10
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X10,sK6)
      | ~ v1_funct_2(X10,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f143,f55])).

fof(f143,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X10,sK6)
      | sK6 = X10
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X10,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f119,f56])).

fof(f119,plain,(
    ! [X10] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X10,sK6)
      | sK6 = X10
      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X10,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X10) ) ),
    inference(resolution,[],[f58,f86])).

fof(f1436,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f1325,f52])).

fof(f932,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f931])).

fof(f931,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f930,f45])).

fof(f930,plain,
    ( v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f929,f46])).

fof(f929,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f928,f47])).

fof(f928,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f927,f52])).

fof(f927,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f926,f113])).

fof(f113,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f926,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f661,f54])).

fof(f661,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK5,X0)
      | m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3))))
      | ~ m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f660,f51])).

fof(f660,plain,(
    ! [X0] :
      ( m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3))))
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f659,f55])).

fof(f659,plain,(
    ! [X0] :
      ( m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f650,f56])).

fof(f650,plain,(
    ! [X0] :
      ( m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f164,f58])).

fof(f164,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f163,f48])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f162,f49])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f161,f50])).

fof(f161,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f160,f53])).

fof(f160,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f159,f59])).

fof(f159,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f148,f60])).

fof(f148,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK5,X3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f62,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f758,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f756,f45])).

fof(f756,plain,
    ( v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f755,f46])).

fof(f755,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f754,f47])).

fof(f754,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f753,f48])).

fof(f753,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f752,f49])).

fof(f752,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f751,f50])).

fof(f751,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f750,f51])).

fof(f750,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f749,f52])).

fof(f749,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f748,f53])).

fof(f748,plain,
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
    inference(subsumption_resolution,[],[f747,f54])).

fof(f747,plain,
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
    inference(subsumption_resolution,[],[f746,f55])).

fof(f746,plain,
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
    inference(subsumption_resolution,[],[f745,f56])).

fof(f745,plain,
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
    inference(subsumption_resolution,[],[f744,f58])).

fof(f744,plain,
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
    inference(subsumption_resolution,[],[f743,f59])).

fof(f743,plain,
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
    inference(subsumption_resolution,[],[f742,f60])).

fof(f742,plain,
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
    inference(subsumption_resolution,[],[f741,f62])).

fof(f741,plain,
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
    inference(resolution,[],[f105,f92])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f740,plain,
    ( spl8_46
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f735,f111,f103,f737])).

fof(f735,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(global_subsumption,[],[f696,f734])).

fof(f734,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(subsumption_resolution,[],[f733,f45])).

fof(f733,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f732,f46])).

fof(f732,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f731,f47])).

fof(f731,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f730,f48])).

fof(f730,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f729,f49])).

fof(f729,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f728,f50])).

fof(f728,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f727,f51])).

fof(f727,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f726,f52])).

fof(f726,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f725,f53])).

fof(f725,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f724,f54])).

fof(f724,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f723,f55])).

fof(f723,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f722,f56])).

fof(f722,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f721,f58])).

fof(f721,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f720,f59])).

fof(f720,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f719,f60])).

fof(f719,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f188,f62])).

fof(f188,plain,
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
    inference(resolution,[],[f63,f95])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_tmap_1)).

fof(f63,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f696,plain,(
    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subsumption_resolution,[],[f695,f45])).

fof(f695,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f694,f46])).

fof(f694,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f693,f47])).

fof(f693,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f686,f52])).

fof(f686,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f509,f54])).

fof(f509,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK5,X0)
      | v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7))
      | ~ m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f508,f51])).

fof(f508,plain,(
    ! [X0] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7))
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f507,f55])).

fof(f507,plain,(
    ! [X0] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f500,f56])).

fof(f500,plain,(
    ! [X0] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7))
      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f158,f58])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f157,f48])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f156,f49])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f155,f50])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f153,f59])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f147,f60])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7))
      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(sK7)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK5,X0)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f62,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
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

fof(f718,plain,
    ( spl8_45
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f713,f111,f103,f715])).

fof(f713,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(global_subsumption,[],[f696,f712])).

fof(f712,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(subsumption_resolution,[],[f711,f45])).

fof(f711,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f710,f46])).

fof(f710,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f709,f47])).

fof(f709,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f708,f48])).

fof(f708,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f707,f49])).

fof(f707,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f706,f50])).

fof(f706,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f705,f51])).

fof(f705,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f704,f52])).

fof(f704,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f703,f53])).

fof(f703,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f702,f54])).

fof(f702,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f701,f55])).

fof(f701,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f700,f56])).

fof(f700,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f699,f58])).

fof(f699,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f698,f59])).

fof(f698,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f697,f60])).

fof(f697,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
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
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f189,plain,
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
    inference(resolution,[],[f63,f94])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f692,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f690,f45])).

fof(f690,plain,
    ( v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f689,f46])).

fof(f689,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f688,f47])).

fof(f688,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f687,f52])).

fof(f687,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f686,f101])).

fof(f101,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f114,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f65,f111,f107,f103,f99])).

fof(f65,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (24536)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (24545)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (24535)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (24538)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (24539)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (24553)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (24541)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (24542)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (24534)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (24537)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (24549)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (24557)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (24547)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (24548)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (24550)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (24543)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (24554)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (24551)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (24552)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (24546)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (24556)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (24558)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (24561)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (24541)Refutation not found, incomplete strategy% (24541)------------------------------
% 0.21/0.54  % (24541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24541)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24541)Memory used [KB]: 10874
% 0.21/0.54  % (24541)Time elapsed: 0.130 s
% 0.21/0.54  % (24541)------------------------------
% 0.21/0.54  % (24541)------------------------------
% 0.21/0.54  % (24560)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (24544)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (24559)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (24535)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1743,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f114,f692,f718,f740,f758,f932,f1486,f1595,f1616,f1658,f1738,f1741])).
% 0.21/0.57  fof(f1741,plain,(
% 0.21/0.57    ~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104 | spl8_106),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1740])).
% 0.21/0.57  fof(f1740,plain,(
% 0.21/0.57    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104 | spl8_106)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1739,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f34,f33,f32,f31,f30,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_tsep_1(sK2,sK4,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5))) & r4_tsep_1(sK2,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_tsep_1(sK2,sK4,X3),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5))) & r4_tsep_1(sK2,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X3),X4),k3_tmap_1(sK2,sK3,X3,k2_tsep_1(sK2,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X4),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X4),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.58  fof(f8,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.58    inference(negated_conjecture,[],[f7])).
% 0.21/0.58  fof(f7,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).
% 0.21/0.58  fof(f1739,plain,(
% 0.21/0.58    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104 | spl8_106)),
% 0.21/0.58    inference(forward_demodulation,[],[f1478,f1685])).
% 0.21/0.58  fof(f1685,plain,(
% 0.21/0.58    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1684,f1329])).
% 0.21/0.58  fof(f1329,plain,(
% 0.21/0.58    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(resolution,[],[f1290,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    m1_pre_topc(sK5,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1290,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1289,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ~v2_struct_0(sK4)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1289,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1288,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    m1_pre_topc(sK4,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1288,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1287,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ~v2_struct_0(sK5)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1287,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1286,f54])).
% 0.21/0.58  fof(f1286,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1285,f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ~v2_struct_0(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1285,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1284,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    v2_pre_topc(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1284,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1283,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    l1_pre_topc(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1283,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f1282])).
% 0.21/0.58  fof(f1282,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(resolution,[],[f1012,f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.21/0.58  fof(f1012,plain,(
% 0.21/0.58    ( ! [X10,X11] : (~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10) | ~m1_pre_topc(X11,X10) | v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1011,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ~v2_struct_0(sK3)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1011,plain,(
% 0.21/0.58    ( ! [X10,X11] : (v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_pre_topc(X11,X10) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10) | v2_struct_0(sK3) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1010,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    v2_pre_topc(sK3)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1010,plain,(
% 0.21/0.58    ( ! [X10,X11] : (v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_pre_topc(X11,X10) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1009,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    l1_pre_topc(sK3)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1009,plain,(
% 0.21/0.58    ( ! [X10,X11] : (v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_pre_topc(X11,X10) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1008,f100])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f99])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    spl8_1 <=> v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.58  fof(f1008,plain,(
% 0.21/0.58    ( ! [X10,X11] : (v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(X11,X10) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | (~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f945,f104])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~spl8_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f103])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    spl8_2 <=> v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.58  fof(f945,plain,(
% 0.21/0.58    ( ! [X10,X11] : (v1_funct_1(k3_tmap_1(X10,sK3,k1_tsep_1(sK2,sK4,sK5),X11,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(X11,X10) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X10) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10)) ) | ~spl8_4),
% 0.21/0.58    inference(resolution,[],[f112,f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~spl8_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f111])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    spl8_4 <=> m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.58  fof(f1684,plain,(
% 0.21/0.58    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1683,f1469])).
% 0.21/0.58  fof(f1469,plain,(
% 0.21/0.58    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl8_104),
% 0.21/0.58    inference(avatar_component_clause,[],[f1468])).
% 0.21/0.58  fof(f1468,plain,(
% 0.21/0.58    spl8_104 <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).
% 0.21/0.58  fof(f1683,plain,(
% 0.21/0.58    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1668,f717])).
% 0.21/0.58  fof(f717,plain,(
% 0.21/0.58    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~spl8_45),
% 0.21/0.58    inference(avatar_component_clause,[],[f715])).
% 0.21/0.58  fof(f715,plain,(
% 0.21/0.58    spl8_45 <=> r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.21/0.58  fof(f1668,plain,(
% 0.21/0.58    sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(resolution,[],[f1437,f176])).
% 0.21/0.58  fof(f176,plain,(
% 0.21/0.58    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | sK7 = X10 | ~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X10,sK7) | ~v1_funct_2(X10,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(X10)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f175,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    v1_funct_1(sK7)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f175,plain,(
% 0.21/0.58    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X10,sK7) | sK7 = X10 | ~v1_funct_1(sK7) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(X10,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(X10)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f151,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X10,sK7) | sK7 = X10 | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(X10,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(X10)) )),
% 0.21/0.58    inference(resolution,[],[f62,f86])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.58  fof(f1437,plain,(
% 0.21/0.58    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(resolution,[],[f1325,f54])).
% 0.21/0.58  fof(f1325,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1324,f51])).
% 0.21/0.58  fof(f1324,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1323,f52])).
% 0.21/0.58  fof(f1323,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1322,f53])).
% 0.21/0.58  fof(f1322,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1321,f54])).
% 0.21/0.58  fof(f1321,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1320,f45])).
% 0.21/0.58  fof(f1320,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1319,f46])).
% 0.21/0.58  fof(f1319,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1318,f47])).
% 0.21/0.58  fof(f1318,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f1317])).
% 0.21/0.58  fof(f1317,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(resolution,[],[f1017,f85])).
% 0.21/0.58  fof(f1017,plain,(
% 0.21/0.58    ( ! [X12,X13] : (~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12) | ~m1_pre_topc(X13,X12) | m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3)))) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1016,f48])).
% 0.21/0.58  fof(f1016,plain,(
% 0.21/0.58    ( ! [X12,X13] : (m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3)))) | ~m1_pre_topc(X13,X12) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12) | v2_struct_0(sK3) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1015,f49])).
% 0.21/0.58  fof(f1015,plain,(
% 0.21/0.58    ( ! [X12,X13] : (m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3)))) | ~m1_pre_topc(X13,X12) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1014,f50])).
% 0.21/0.58  fof(f1014,plain,(
% 0.21/0.58    ( ! [X12,X13] : (m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3)))) | ~m1_pre_topc(X13,X12) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1013,f100])).
% 0.21/0.58  fof(f1013,plain,(
% 0.21/0.58    ( ! [X12,X13] : (m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3)))) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(X13,X12) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | (~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f946,f104])).
% 0.21/0.58  fof(f946,plain,(
% 0.21/0.58    ( ! [X12,X13] : (m1_subset_1(k3_tmap_1(X12,sK3,k1_tsep_1(sK2,sK4,sK5),X13,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(X13,X12) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),X12) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12)) ) | ~spl8_4),
% 0.21/0.58    inference(resolution,[],[f112,f90])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f1478,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_106),
% 0.21/0.58    inference(avatar_component_clause,[],[f1476])).
% 0.21/0.58  fof(f1476,plain,(
% 0.21/0.58    spl8_106 <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).
% 0.21/0.58  fof(f1738,plain,(
% 0.21/0.58    ~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104 | spl8_105),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1737])).
% 0.21/0.58  fof(f1737,plain,(
% 0.21/0.58    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104 | spl8_105)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1732,f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    v5_pre_topc(sK7,sK5,sK3)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1732,plain,(
% 0.21/0.58    ~v5_pre_topc(sK7,sK5,sK3) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_45 | ~spl8_104 | spl8_105)),
% 0.21/0.58    inference(backward_demodulation,[],[f1474,f1685])).
% 0.21/0.58  fof(f1474,plain,(
% 0.21/0.58    ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | spl8_105),
% 0.21/0.58    inference(avatar_component_clause,[],[f1472])).
% 0.21/0.58  fof(f1472,plain,(
% 0.21/0.58    spl8_105 <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).
% 0.21/0.58  fof(f1658,plain,(
% 0.21/0.58    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1657])).
% 0.21/0.58  fof(f1657,plain,(
% 0.21/0.58    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1656,f45])).
% 0.21/0.58  fof(f1656,plain,(
% 0.21/0.58    v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1655,f47])).
% 0.21/0.58  fof(f1655,plain,(
% 0.21/0.58    ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1654,f51])).
% 0.21/0.58  fof(f1654,plain,(
% 0.21/0.58    v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1653,f52])).
% 0.21/0.58  fof(f1653,plain,(
% 0.21/0.58    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1652,f53])).
% 0.21/0.58  fof(f1652,plain,(
% 0.21/0.58    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1651,f54])).
% 0.21/0.58  fof(f1651,plain,(
% 0.21/0.58    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(resolution,[],[f1641,f85])).
% 0.21/0.58  fof(f1641,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1640,f45])).
% 0.21/0.58  fof(f1640,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1639,f46])).
% 0.21/0.58  fof(f1639,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1638,f47])).
% 0.21/0.58  fof(f1638,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1637,f48])).
% 0.21/0.58  fof(f1637,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1636,f49])).
% 0.21/0.58  fof(f1636,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1635,f50])).
% 0.21/0.58  fof(f1635,plain,(
% 0.21/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1634,f54])).
% 0.21/0.58  fof(f1634,plain,(
% 0.21/0.58    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1633,f100])).
% 0.21/0.58  fof(f1633,plain,(
% 0.21/0.58    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1632,f104])).
% 0.21/0.58  fof(f1632,plain,(
% 0.21/0.58    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_104)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1631,f112])).
% 0.21/0.58  fof(f1631,plain,(
% 0.21/0.58    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_104),
% 0.21/0.58    inference(resolution,[],[f1470,f89])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f1470,plain,(
% 0.21/0.58    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | spl8_104),
% 0.21/0.58    inference(avatar_component_clause,[],[f1468])).
% 0.21/0.58  fof(f1616,plain,(
% 0.21/0.58    ~spl8_104 | ~spl8_105 | ~spl8_106 | ~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_107),
% 0.21/0.58    inference(avatar_split_clause,[],[f1615,f1483,f111,f107,f103,f99,f1476,f1472,f1468])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    spl8_3 <=> v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.58  fof(f1483,plain,(
% 0.21/0.58    spl8_107 <=> sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).
% 0.21/0.58  fof(f1615,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_107)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1614,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    v1_funct_1(sK6)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1614,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_107)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1613,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1613,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_107)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1612,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    v5_pre_topc(sK6,sK4,sK3)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1612,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(sK6,sK4,sK3) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_107)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1611,f1034])).
% 0.21/0.58  fof(f1034,plain,(
% 0.21/0.58    ~sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1032,f109])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | spl8_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f107])).
% 0.21/0.58  fof(f1032,plain,(
% 0.21/0.58    ~sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(resolution,[],[f961,f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X4,X3,X2,X1,X0) | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 0.21/0.58    inference(rectify,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 0.21/0.58    inference(flattening,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.58  fof(f961,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f960,f45])).
% 0.21/0.58  fof(f960,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f959,f46])).
% 0.21/0.58  fof(f959,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f958,f47])).
% 0.21/0.58  fof(f958,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f957,f48])).
% 0.21/0.58  fof(f957,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f956,f49])).
% 0.21/0.58  fof(f956,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f955,f50])).
% 0.21/0.58  fof(f955,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f954,f51])).
% 0.21/0.58  fof(f954,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f953,f52])).
% 0.21/0.58  fof(f953,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f952,f53])).
% 0.21/0.58  fof(f952,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f951,f54])).
% 0.21/0.58  fof(f951,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f950,f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    r4_tsep_1(sK2,sK4,sK5)),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f950,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f949,f100])).
% 0.21/0.58  fof(f949,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f937,f104])).
% 0.21/0.58  fof(f937,plain,(
% 0.21/0.58    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl8_4),
% 0.21/0.58    inference(resolution,[],[f112,f80])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | sP1(X0,X2,X4,X3,X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(definition_folding,[],[f15,f27,f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).
% 0.21/0.58  fof(f1611,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | ~v5_pre_topc(sK6,sK4,sK3) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_107)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1610,f1329])).
% 0.21/0.58  fof(f1610,plain,(
% 0.21/0.58    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | ~v5_pre_topc(sK6,sK4,sK3) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~spl8_107),
% 0.21/0.58    inference(subsumption_resolution,[],[f1608,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f1608,plain,(
% 0.21/0.58    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | ~v5_pre_topc(sK6,sK4,sK3) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~spl8_107),
% 0.21/0.58    inference(superposition,[],[f79,f1485])).
% 0.21/0.58  fof(f1485,plain,(
% 0.21/0.58    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_107),
% 0.21/0.58    inference(avatar_component_clause,[],[f1483])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP0(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 0.21/0.58    inference(rectify,[],[f40])).
% 1.68/0.58  fof(f40,plain,(
% 1.68/0.58    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 1.68/0.58    inference(flattening,[],[f39])).
% 1.68/0.58  fof(f39,plain,(
% 1.68/0.58    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 1.68/0.58    inference(nnf_transformation,[],[f26])).
% 1.68/0.58  fof(f1595,plain,(
% 1.68/0.58    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f1594])).
% 1.68/0.58  fof(f1594,plain,(
% 1.68/0.58    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1593,f45])).
% 1.68/0.58  fof(f1593,plain,(
% 1.68/0.58    v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1592,f47])).
% 1.68/0.58  fof(f1592,plain,(
% 1.68/0.58    ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1591,f51])).
% 1.68/0.58  fof(f1591,plain,(
% 1.68/0.58    v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1590,f52])).
% 1.68/0.58  fof(f1590,plain,(
% 1.68/0.58    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1589,f53])).
% 1.68/0.58  fof(f1589,plain,(
% 1.68/0.58    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1588,f54])).
% 1.68/0.58  fof(f1588,plain,(
% 1.68/0.58    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(resolution,[],[f1587,f85])).
% 1.68/0.58  fof(f1587,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1586,f45])).
% 1.68/0.58  fof(f1586,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1585,f46])).
% 1.68/0.58  fof(f1585,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1584,f47])).
% 1.68/0.58  fof(f1584,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1583,f48])).
% 1.68/0.58  fof(f1583,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1582,f49])).
% 1.68/0.58  fof(f1582,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1581,f50])).
% 1.68/0.58  fof(f1581,plain,(
% 1.68/0.58    ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1580,f52])).
% 1.68/0.58  fof(f1580,plain,(
% 1.68/0.58    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1579,f100])).
% 1.68/0.58  fof(f1579,plain,(
% 1.68/0.58    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1578,f104])).
% 1.68/0.58  fof(f1578,plain,(
% 1.68/0.58    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_102)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1577,f112])).
% 1.68/0.58  fof(f1577,plain,(
% 1.68/0.58    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_102),
% 1.68/0.58    inference(resolution,[],[f1462,f89])).
% 1.68/0.58  fof(f1462,plain,(
% 1.68/0.58    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | spl8_102),
% 1.68/0.58    inference(avatar_component_clause,[],[f1460])).
% 1.68/0.58  fof(f1460,plain,(
% 1.68/0.58    spl8_102 <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 1.68/0.58  fof(f1486,plain,(
% 1.68/0.58    ~spl8_102 | spl8_107 | ~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_46),
% 1.68/0.58    inference(avatar_split_clause,[],[f1481,f737,f111,f103,f99,f1483,f1460])).
% 1.68/0.58  fof(f737,plain,(
% 1.68/0.58    spl8_46 <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.68/0.58  fof(f1481,plain,(
% 1.68/0.58    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_46)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1480,f1328])).
% 1.68/0.58  fof(f1328,plain,(
% 1.68/0.58    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 1.68/0.58    inference(resolution,[],[f1290,f52])).
% 1.68/0.58  fof(f1480,plain,(
% 1.68/0.58    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_46)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1441,f739])).
% 1.68/0.58  fof(f739,plain,(
% 1.68/0.58    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~spl8_46),
% 1.68/0.58    inference(avatar_component_clause,[],[f737])).
% 1.68/0.58  fof(f1441,plain,(
% 1.68/0.58    sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 1.68/0.58    inference(resolution,[],[f1436,f144])).
% 1.68/0.58  fof(f144,plain,(
% 1.68/0.58    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | sK6 = X10 | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X10,sK6) | ~v1_funct_2(X10,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X10)) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f143,f55])).
% 1.68/0.58  fof(f143,plain,(
% 1.68/0.58    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X10,sK6) | sK6 = X10 | ~v1_funct_1(sK6) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X10,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X10)) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f119,f56])).
% 1.68/0.58  fof(f119,plain,(
% 1.68/0.58    ( ! [X10] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X10,sK6) | sK6 = X10 | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X10,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X10)) )),
% 1.68/0.58    inference(resolution,[],[f58,f86])).
% 1.68/0.58  fof(f1436,plain,(
% 1.68/0.58    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | (~spl8_1 | ~spl8_2 | ~spl8_4)),
% 1.68/0.58    inference(resolution,[],[f1325,f52])).
% 1.68/0.58  fof(f932,plain,(
% 1.68/0.58    spl8_4),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f931])).
% 1.68/0.58  fof(f931,plain,(
% 1.68/0.58    $false | spl8_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f930,f45])).
% 1.68/0.58  fof(f930,plain,(
% 1.68/0.58    v2_struct_0(sK2) | spl8_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f929,f46])).
% 1.68/0.58  fof(f929,plain,(
% 1.68/0.58    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f928,f47])).
% 1.68/0.58  fof(f928,plain,(
% 1.68/0.58    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f927,f52])).
% 1.68/0.58  fof(f927,plain,(
% 1.68/0.58    ~m1_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f926,f113])).
% 1.68/0.58  fof(f113,plain,(
% 1.68/0.58    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | spl8_4),
% 1.68/0.58    inference(avatar_component_clause,[],[f111])).
% 1.68/0.58  fof(f926,plain,(
% 1.68/0.58    m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~m1_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.58    inference(resolution,[],[f661,f54])).
% 1.68/0.59  fof(f661,plain,(
% 1.68/0.59    ( ! [X0] : (~m1_pre_topc(sK5,X0) | m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3)))) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f660,f51])).
% 1.68/0.59  fof(f660,plain,(
% 1.68/0.59    ( ! [X0] : (m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3)))) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f659,f55])).
% 1.68/0.59  fof(f659,plain,(
% 1.68/0.59    ( ! [X0] : (m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f650,f56])).
% 1.68/0.59  fof(f650,plain,(
% 1.68/0.59    ( ! [X0] : (m1_subset_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(resolution,[],[f164,f58])).
% 1.68/0.59  fof(f164,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f163,f48])).
% 1.68/0.59  fof(f163,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f162,f49])).
% 1.68/0.59  fof(f162,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f161,f50])).
% 1.68/0.59  fof(f161,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f160,f53])).
% 1.68/0.59  fof(f160,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | v2_struct_0(sK5) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f159,f59])).
% 1.68/0.59  fof(f159,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_1(sK7) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | v2_struct_0(sK5) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f148,f60])).
% 1.68/0.59  fof(f148,plain,(
% 1.68/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k10_tmap_1(X3,sK3,X4,sK5,X5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK5,X3) | v2_struct_0(sK5) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.68/0.59    inference(resolution,[],[f62,f93])).
% 1.68/0.59  fof(f93,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f25])).
% 1.68/0.59  fof(f25,plain,(
% 1.68/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.59    inference(flattening,[],[f24])).
% 1.68/0.59  fof(f24,plain,(
% 1.68/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.59    inference(ennf_transformation,[],[f3])).
% 1.68/0.59  fof(f3,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.68/0.59  fof(f758,plain,(
% 1.68/0.59    spl8_2),
% 1.68/0.59    inference(avatar_contradiction_clause,[],[f757])).
% 1.68/0.59  fof(f757,plain,(
% 1.68/0.59    $false | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f756,f45])).
% 1.68/0.59  fof(f756,plain,(
% 1.68/0.59    v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f755,f46])).
% 1.68/0.59  fof(f755,plain,(
% 1.68/0.59    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f754,f47])).
% 1.68/0.59  fof(f754,plain,(
% 1.68/0.59    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f753,f48])).
% 1.68/0.59  fof(f753,plain,(
% 1.68/0.59    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f752,f49])).
% 1.68/0.59  fof(f752,plain,(
% 1.68/0.59    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f751,f50])).
% 1.68/0.59  fof(f751,plain,(
% 1.68/0.59    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f750,f51])).
% 1.68/0.59  fof(f750,plain,(
% 1.68/0.59    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f749,f52])).
% 1.68/0.59  fof(f749,plain,(
% 1.68/0.59    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f748,f53])).
% 1.68/0.59  fof(f748,plain,(
% 1.68/0.59    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f747,f54])).
% 1.68/0.59  fof(f747,plain,(
% 1.68/0.59    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f746,f55])).
% 1.68/0.59  fof(f746,plain,(
% 1.68/0.59    ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f745,f56])).
% 1.68/0.59  fof(f745,plain,(
% 1.68/0.59    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f744,f58])).
% 1.68/0.59  fof(f744,plain,(
% 1.68/0.59    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f743,f59])).
% 1.68/0.59  fof(f743,plain,(
% 1.68/0.59    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f742,f60])).
% 1.68/0.59  fof(f742,plain,(
% 1.68/0.59    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(subsumption_resolution,[],[f741,f62])).
% 1.68/0.59  fof(f741,plain,(
% 1.68/0.59    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_2),
% 1.68/0.59    inference(resolution,[],[f105,f92])).
% 1.68/0.59  fof(f92,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f25])).
% 1.68/0.59  fof(f105,plain,(
% 1.68/0.59    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | spl8_2),
% 1.68/0.59    inference(avatar_component_clause,[],[f103])).
% 1.68/0.59  fof(f740,plain,(
% 1.68/0.59    spl8_46 | ~spl8_2 | ~spl8_4),
% 1.68/0.59    inference(avatar_split_clause,[],[f735,f111,f103,f737])).
% 1.68/0.59  fof(f735,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 1.68/0.59    inference(global_subsumption,[],[f696,f734])).
% 1.68/0.59  fof(f734,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 1.68/0.59    inference(subsumption_resolution,[],[f733,f45])).
% 1.68/0.59  fof(f733,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f732,f46])).
% 1.68/0.59  fof(f732,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f731,f47])).
% 1.68/0.59  fof(f731,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f730,f48])).
% 1.68/0.59  fof(f730,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f729,f49])).
% 1.68/0.59  fof(f729,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f728,f50])).
% 1.68/0.59  fof(f728,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f727,f51])).
% 1.68/0.59  fof(f727,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f726,f52])).
% 1.68/0.59  fof(f726,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f725,f53])).
% 1.68/0.59  fof(f725,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f724,f54])).
% 1.68/0.59  fof(f724,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f723,f55])).
% 1.68/0.59  fof(f723,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f722,f56])).
% 1.68/0.59  fof(f722,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f721,f58])).
% 1.68/0.59  fof(f721,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f720,f59])).
% 1.68/0.59  fof(f720,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f719,f60])).
% 1.68/0.59  fof(f719,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f188,f62])).
% 1.68/0.59  fof(f188,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(resolution,[],[f63,f95])).
% 1.68/0.59  fof(f95,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(equality_resolution,[],[f81])).
% 1.68/0.59  fof(f81,plain,(
% 1.68/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f43])).
% 1.68/0.59  fof(f43,plain,(
% 1.68/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.59    inference(flattening,[],[f42])).
% 1.68/0.59  fof(f42,plain,(
% 1.68/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.59    inference(nnf_transformation,[],[f17])).
% 1.68/0.59  fof(f17,plain,(
% 1.68/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.59    inference(flattening,[],[f16])).
% 1.68/0.59  fof(f16,plain,(
% 1.68/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6))) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.59    inference(ennf_transformation,[],[f10])).
% 1.68/0.59  fof(f10,plain,(
% 1.68/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 1.68/0.59    inference(pure_predicate_removal,[],[f2])).
% 1.68/0.59  fof(f2,axiom,(
% 1.68/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r1_tsep_1(X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_tmap_1)).
% 1.68/0.59  fof(f63,plain,(
% 1.68/0.59    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))),
% 1.68/0.59    inference(cnf_transformation,[],[f35])).
% 1.68/0.59  fof(f696,plain,(
% 1.68/0.59    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.68/0.59    inference(subsumption_resolution,[],[f695,f45])).
% 1.68/0.59  fof(f695,plain,(
% 1.68/0.59    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f694,f46])).
% 1.68/0.59  fof(f694,plain,(
% 1.68/0.59    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f693,f47])).
% 1.68/0.59  fof(f693,plain,(
% 1.68/0.59    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f686,f52])).
% 1.68/0.59  fof(f686,plain,(
% 1.68/0.59    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(resolution,[],[f509,f54])).
% 1.68/0.59  fof(f509,plain,(
% 1.68/0.59    ( ! [X0] : (~m1_pre_topc(sK5,X0) | v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f508,f51])).
% 1.68/0.59  fof(f508,plain,(
% 1.68/0.59    ( ! [X0] : (v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f507,f55])).
% 1.68/0.59  fof(f507,plain,(
% 1.68/0.59    ( ! [X0] : (v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f500,f56])).
% 1.68/0.59  fof(f500,plain,(
% 1.68/0.59    ( ! [X0] : (v1_funct_1(k10_tmap_1(X0,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(resolution,[],[f158,f58])).
% 1.68/0.59  fof(f158,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f157,f48])).
% 1.68/0.59  fof(f157,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f156,f49])).
% 1.68/0.59  fof(f156,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f155,f50])).
% 1.68/0.59  fof(f155,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f154,f53])).
% 1.68/0.59  fof(f154,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK5) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f153,f59])).
% 1.68/0.59  fof(f153,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~v1_funct_1(sK7) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK5) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f147,f60])).
% 1.68/0.59  fof(f147,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k10_tmap_1(X0,sK3,X1,sK5,X2,sK7)) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK5) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(resolution,[],[f62,f91])).
% 1.68/0.59  fof(f91,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f25])).
% 1.68/0.59  fof(f718,plain,(
% 1.68/0.59    spl8_45 | ~spl8_2 | ~spl8_4),
% 1.68/0.59    inference(avatar_split_clause,[],[f713,f111,f103,f715])).
% 1.68/0.59  fof(f713,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 1.68/0.59    inference(global_subsumption,[],[f696,f712])).
% 1.68/0.59  fof(f712,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 1.68/0.59    inference(subsumption_resolution,[],[f711,f45])).
% 1.68/0.59  fof(f711,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f710,f46])).
% 1.68/0.59  fof(f710,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f709,f47])).
% 1.68/0.59  fof(f709,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f708,f48])).
% 1.68/0.59  fof(f708,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f707,f49])).
% 1.68/0.59  fof(f707,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f706,f50])).
% 1.68/0.59  fof(f706,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f705,f51])).
% 1.68/0.59  fof(f705,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f704,f52])).
% 1.68/0.59  fof(f704,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f703,f53])).
% 1.68/0.59  fof(f703,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f702,f54])).
% 1.68/0.59  fof(f702,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f701,f55])).
% 1.68/0.59  fof(f701,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f700,f56])).
% 1.68/0.59  fof(f700,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f699,f58])).
% 1.68/0.59  fof(f699,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f698,f59])).
% 1.68/0.59  fof(f698,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f697,f60])).
% 1.68/0.59  fof(f697,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(subsumption_resolution,[],[f189,f62])).
% 1.68/0.59  fof(f189,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.68/0.59    inference(resolution,[],[f63,f94])).
% 1.68/0.59  fof(f94,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(equality_resolution,[],[f82])).
% 1.68/0.59  fof(f82,plain,(
% 1.68/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f43])).
% 1.68/0.59  fof(f692,plain,(
% 1.68/0.59    spl8_1),
% 1.68/0.59    inference(avatar_contradiction_clause,[],[f691])).
% 1.68/0.59  fof(f691,plain,(
% 1.68/0.59    $false | spl8_1),
% 1.68/0.59    inference(subsumption_resolution,[],[f690,f45])).
% 1.68/0.59  fof(f690,plain,(
% 1.68/0.59    v2_struct_0(sK2) | spl8_1),
% 1.68/0.59    inference(subsumption_resolution,[],[f689,f46])).
% 1.68/0.59  fof(f689,plain,(
% 1.68/0.59    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.68/0.59    inference(subsumption_resolution,[],[f688,f47])).
% 1.68/0.59  fof(f688,plain,(
% 1.68/0.59    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.68/0.59    inference(subsumption_resolution,[],[f687,f52])).
% 1.68/0.59  fof(f687,plain,(
% 1.68/0.59    ~m1_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 1.68/0.59    inference(subsumption_resolution,[],[f686,f101])).
% 1.68/0.59  fof(f101,plain,(
% 1.68/0.59    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_1),
% 1.68/0.59    inference(avatar_component_clause,[],[f99])).
% 1.68/0.59  fof(f114,plain,(
% 1.68/0.59    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 1.68/0.59    inference(avatar_split_clause,[],[f65,f111,f107,f103,f99])).
% 1.68/0.59  fof(f65,plain,(
% 1.68/0.59    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.68/0.59    inference(cnf_transformation,[],[f35])).
% 1.68/0.59  % SZS output end Proof for theBenchmark
% 1.68/0.59  % (24535)------------------------------
% 1.68/0.59  % (24535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (24535)Termination reason: Refutation
% 1.68/0.59  
% 1.68/0.59  % (24535)Memory used [KB]: 11897
% 1.68/0.59  % (24535)Time elapsed: 0.155 s
% 1.68/0.59  % (24535)------------------------------
% 1.68/0.59  % (24535)------------------------------
% 1.83/0.61  % (24528)Success in time 0.241 s
%------------------------------------------------------------------------------

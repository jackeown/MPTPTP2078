%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:51 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  287 (2003 expanded)
%              Number of leaves         :   28 (1039 expanded)
%              Depth                    :   28
%              Number of atoms          : 2390 (51149 expanded)
%              Number of equality atoms :   32 (1816 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f157,f178,f211,f267,f277,f287,f300,f306,f331,f345,f372,f393,f407,f413])).

fof(f413,plain,
    ( ~ spl8_12
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl8_12
    | spl8_14 ),
    inference(subsumption_resolution,[],[f408,f53])).

fof(f53,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r4_tsep_1(sK2,sK4,sK5)
    & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & sK2 = k1_tsep_1(sK2,sK4,sK5)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f27,f26,f25,f24,f23,f22])).

fof(f22,plain,
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK2,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK2 = k1_tsep_1(sK2,X2,X3)
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

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1)
                          | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                        & r4_tsep_1(sK2,X2,X3)
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK2 = k1_tsep_1(sK2,X2,X3)
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
                      ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                        | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),sK2,sK3)
                        | ~ v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3))
                        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5)) )
                      & r4_tsep_1(sK2,X2,X3)
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(X5,X3,sK3)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                  & v5_pre_topc(X4,X2,sK3)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & sK2 = k1_tsep_1(sK2,X2,X3)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),sK2,sK3)
                      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3))
                      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5)) )
                    & r4_tsep_1(sK2,X2,X3)
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(X5,X3,sK3)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                & v5_pre_topc(X4,X2,sK3)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & sK2 = k1_tsep_1(sK2,X2,X3)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),sK2,sK3)
                    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3))
                    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)) )
                  & r4_tsep_1(sK2,sK4,X3)
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X4)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(X5,X3,sK3)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              & v5_pre_topc(X4,sK4,sK3)
              & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & sK2 = k1_tsep_1(sK2,sK4,X3)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),sK2,sK3)
                  | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3))
                  | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)) )
                & r4_tsep_1(sK2,sK4,X3)
                & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X4)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(X5,X3,sK3)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            & v5_pre_topc(X4,sK4,sK3)
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & sK2 = k1_tsep_1(sK2,sK4,X3)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),sK2,sK3)
                | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3))
                | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)) )
              & r4_tsep_1(sK2,sK4,sK5)
              & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X4)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(X5,sK5,sK3)
              & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          & v5_pre_topc(X4,sK4,sK3)
          & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & sK2 = k1_tsep_1(sK2,sK4,sK5)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),sK2,sK3)
              | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3))
              | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)) )
            & r4_tsep_1(sK2,sK4,sK5)
            & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X5)
            & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(X5,sK5,sK3)
            & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v5_pre_topc(X4,sK4,sK3)
        & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),sK2,sK3)
            | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(sK2),u1_struct_0(sK3))
            | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)) )
          & r4_tsep_1(sK2,sK4,sK5)
          & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),X5)
          & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),sK6)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(X5,sK5,sK3)
          & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      & v5_pre_topc(sK6,sK4,sK3)
      & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),sK2,sK3)
          | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(sK2),u1_struct_0(sK3))
          | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)) )
        & r4_tsep_1(sK2,sK4,sK5)
        & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),X5)
        & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),sK6)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(X5,sK5,sK3)
        & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
        | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
      & r4_tsep_1(sK2,sK4,sK5)
      & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
      & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v5_pre_topc(sK7,sK5,sK3)
      & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK7) ) ),
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

fof(f408,plain,
    ( ~ v5_pre_topc(sK7,sK5,sK3)
    | ~ spl8_12
    | spl8_14 ),
    inference(backward_demodulation,[],[f392,f210])).

fof(f210,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_12
  <=> sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f392,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl8_14
  <=> v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f407,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f405,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f405,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f404,f37])).

fof(f37,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f404,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f403,f38])).

fof(f38,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f403,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f402,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f402,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f401,f40])).

fof(f40,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f401,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f400,f41])).

fof(f41,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f400,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f399,f104])).

fof(f104,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f38,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f399,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f398,f45])).

fof(f45,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f398,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f397,f87])).

fof(f87,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_1
  <=> v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f397,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f396,f91])).

fof(f91,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_2
  <=> v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f396,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f394,f99])).

fof(f99,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_4
  <=> m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f394,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_10 ),
    inference(resolution,[],[f202,f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f202,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_10
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f393,plain,
    ( ~ spl8_11
    | ~ spl8_14
    | ~ spl8_10
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f388,f303,f196,f175,f94,f200,f390,f204])).

fof(f204,plain,
    ( spl8_11
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f94,plain,
    ( spl8_3
  <=> v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f175,plain,
    ( spl8_8
  <=> sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f196,plain,
    ( spl8_9
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f303,plain,
    ( spl8_13
  <=> sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f388,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f387,f47])).

fof(f47,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f387,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f386,f177])).

fof(f177,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f386,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f385,f46])).

fof(f46,plain,(
    sK2 = k1_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f385,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f384,f48])).

fof(f48,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f384,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f383,f177])).

fof(f383,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f382,f46])).

fof(f382,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f381,f49])).

fof(f49,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f381,plain,
    ( ~ v5_pre_topc(sK6,sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f380,f177])).

fof(f380,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f379,f46])).

fof(f379,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f378,f50])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f378,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f377,f177])).

fof(f377,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f376,f46])).

fof(f376,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f375,f197])).

fof(f197,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f375,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f374,f46])).

fof(f374,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f373,f46])).

fof(f373,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f317,f46])).

fof(f317,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f316,f46])).

fof(f316,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_3
    | ~ spl8_13 ),
    inference(resolution,[],[f310,f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f310,plain,
    ( ~ sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | spl8_3
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f308,f96])).

fof(f96,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f308,plain,
    ( ~ sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2)
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ spl8_13 ),
    inference(resolution,[],[f305,f113])).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ sP1(sK2,sK4,X2,sK5,X3)
      | ~ sP0(X3,sK5,X2,sK4,sK2)
      | v5_pre_topc(X2,sK2,X3) ) ),
    inference(superposition,[],[f62,f46])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f305,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f303])).

fof(f372,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f370,f36])).

fof(f370,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f369,f37])).

fof(f369,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f368,f38])).

fof(f368,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f367,f39])).

fof(f367,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f366,f40])).

fof(f366,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f365,f41])).

fof(f365,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f364,f104])).

fof(f364,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f363,f45])).

fof(f363,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f362,f87])).

fof(f362,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f361,f91])).

fof(f361,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f359,f99])).

fof(f359,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_11 ),
    inference(resolution,[],[f206,f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f206,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f204])).

fof(f345,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f343,f36])).

fof(f343,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f342,f37])).

fof(f342,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f341,f38])).

fof(f341,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f340,f39])).

fof(f340,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f339,f40])).

fof(f339,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f338,f41])).

fof(f338,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f337,f104])).

fof(f337,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f336,f43])).

fof(f43,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f336,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f335,f87])).

fof(f335,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f334,f91])).

fof(f334,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f332,f99])).

fof(f332,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_7 ),
    inference(resolution,[],[f173,f78])).

fof(f173,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_7
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f331,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f329,f36])).

fof(f329,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f328,f37])).

fof(f328,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f327,f38])).

fof(f327,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f326,f39])).

fof(f326,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f325,f40])).

fof(f325,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f324,f41])).

fof(f324,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f323,f104])).

fof(f323,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f322,f43])).

fof(f322,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f321,f87])).

fof(f321,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f320,f91])).

fof(f320,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f318,f99])).

fof(f318,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_6 ),
    inference(resolution,[],[f169,f77])).

fof(f169,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_6
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f306,plain,
    ( spl8_13
    | ~ spl8_4
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f301,f90,f86,f98,f303])).

fof(f301,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f288,f87])).

fof(f288,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f91,f227])).

fof(f227,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | sP1(sK2,sK4,X1,sK5,sK3) ) ),
    inference(subsumption_resolution,[],[f226,f39])).

fof(f226,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | v2_struct_0(sK3)
      | sP1(sK2,sK4,X1,sK5,sK3) ) ),
    inference(subsumption_resolution,[],[f223,f40])).

fof(f223,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sP1(sK2,sK4,X1,sK5,sK3) ) ),
    inference(resolution,[],[f221,f41])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(forward_demodulation,[],[f220,f46])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(forward_demodulation,[],[f219,f46])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f218,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(sK2,sK4,X0,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f217,f43])).

fof(f217,plain,(
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
    inference(subsumption_resolution,[],[f216,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f216,plain,(
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
    inference(subsumption_resolution,[],[f215,f45])).

fof(f215,plain,(
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
    inference(resolution,[],[f107,f57])).

fof(f57,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
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
    inference(subsumption_resolution,[],[f106,f36])).

fof(f106,plain,(
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
    inference(subsumption_resolution,[],[f105,f37])).

fof(f105,plain,(
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
    inference(resolution,[],[f38,f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(definition_folding,[],[f11,f20,f19])).

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

fof(f300,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f298,f39])).

fof(f298,plain,
    ( v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f297,f40])).

fof(f297,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f296,f41])).

fof(f296,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f295,f47])).

fof(f295,plain,
    ( ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f294,f48])).

fof(f294,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f293,f50])).

fof(f293,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f292,f51])).

fof(f51,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f291,f52])).

fof(f52,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f291,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f290,f54])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f290,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_4 ),
    inference(resolution,[],[f138,f100])).

fof(f100,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f138,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25) ) ),
    inference(subsumption_resolution,[],[f137,f36])).

fof(f137,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f136,f37])).

fof(f136,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f135,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f134,f42])).

fof(f134,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f133,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f132,f44])).

fof(f132,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f124,plain,(
    ! [X26,X27,X25] :
      ( m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25))))
      | ~ v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25))
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25))))
      | ~ v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25))
      | ~ v1_funct_1(X26)
      | ~ m1_pre_topc(sK5,sK2)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X25)
      | ~ v2_pre_topc(X25)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f81,f46])).

fof(f81,plain,(
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

fof(f287,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f286,f163,f86,f98,f90])).

fof(f163,plain,
    ( spl8_5
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f286,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f285,f36])).

fof(f285,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f284,f37])).

fof(f284,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f283,f38])).

fof(f283,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f282,f39])).

fof(f282,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f281,f40])).

fof(f281,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f280,f41])).

fof(f280,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f279,f104])).

fof(f279,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f278,f43])).

fof(f278,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f180,f87])).

fof(f180,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_5 ),
    inference(resolution,[],[f165,f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f165,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f277,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | ~ spl8_1
    | spl8_9 ),
    inference(avatar_split_clause,[],[f276,f196,f86,f98,f90])).

fof(f276,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f275,f36])).

fof(f275,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f274,f37])).

fof(f274,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f273,f38])).

fof(f273,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f272,f39])).

fof(f272,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f271,f40])).

fof(f271,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f270,f41])).

fof(f270,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f269,f104])).

fof(f269,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f268,f45])).

fof(f268,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_1
    | spl8_9 ),
    inference(subsumption_resolution,[],[f213,f87])).

fof(f213,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_9 ),
    inference(resolution,[],[f198,f76])).

fof(f198,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f267,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f265,f54])).

fof(f265,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f264,f47])).

fof(f264,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f263,f48])).

fof(f263,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f262,f50])).

fof(f262,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f261,f51])).

fof(f261,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f259,f52])).

fof(f259,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl8_2 ),
    inference(resolution,[],[f257,f92])).

fof(f92,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f257,plain,(
    ! [X2,X3] :
      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X3,X2),u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ) ),
    inference(subsumption_resolution,[],[f256,f39])).

fof(f256,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X3)
      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X3,X2),u1_struct_0(sK2),u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f253,f40])).

fof(f253,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X3)
      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X3,X2),u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f131,f41])).

fof(f131,plain,(
    ! [X24,X23,X22] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22) ) ),
    inference(subsumption_resolution,[],[f130,f36])).

fof(f130,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f129,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f128,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f127,f42])).

fof(f127,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f126,f43])).

fof(f126,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f125,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f123,plain,(
    ! [X24,X23,X22] :
      ( v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22))))
      | ~ v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22))
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ m1_pre_topc(sK5,sK2)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f80,f46])).

fof(f80,plain,(
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

fof(f211,plain,
    ( ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f194,f208,f204,f200,f196])).

fof(f194,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f193,f51])).

fof(f193,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f192,f52])).

fof(f192,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f191,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(resolution,[],[f103,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f103,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(backward_demodulation,[],[f56,f46])).

fof(f56,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f178,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f161,f175,f171,f167,f163])).

fof(f161,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f160,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f159,f48])).

fof(f159,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(resolution,[],[f102,f74])).

fof(f102,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(backward_demodulation,[],[f55,f46])).

fof(f55,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f157,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f155,f36])).

fof(f155,plain,
    ( v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f154,f37])).

fof(f154,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f153,f38])).

fof(f153,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f152,f39])).

fof(f152,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f151,f40])).

fof(f151,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f150,f41])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f149,f42])).

fof(f149,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f148,f43])).

fof(f148,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f147,f44])).

fof(f147,plain,
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
    inference(subsumption_resolution,[],[f146,f45])).

fof(f146,plain,
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
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,
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
    inference(subsumption_resolution,[],[f144,f48])).

fof(f144,plain,
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
    inference(subsumption_resolution,[],[f143,f50])).

fof(f143,plain,
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
    inference(subsumption_resolution,[],[f142,f51])).

fof(f142,plain,
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
    inference(subsumption_resolution,[],[f141,f52])).

fof(f141,plain,
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
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,
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
    inference(resolution,[],[f88,f79])).

fof(f79,plain,(
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

fof(f88,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f101,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f58,f98,f94,f90,f86])).

fof(f58,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:37:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (28117)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (28109)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (28108)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (28107)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.47/0.55  % (28099)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.47/0.56  % (28100)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.47/0.56  % (28118)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.47/0.56  % (28102)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.47/0.56  % (28103)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.47/0.57  % (28119)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.47/0.57  % (28121)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.47/0.57  % (28113)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.65/0.57  % (28122)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.65/0.57  % (28104)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.65/0.58  % (28106)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.65/0.58  % (28110)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.65/0.58  % (28116)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.65/0.58  % (28105)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.65/0.59  % (28098)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.65/0.59  % (28101)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.65/0.61  % (28114)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.65/0.61  % (28112)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.65/0.61  % (28115)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.65/0.62  % (28111)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.65/0.62  % (28120)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.65/0.63  % (28123)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.65/0.63  % (28104)Refutation found. Thanks to Tanya!
% 1.65/0.63  % SZS status Theorem for theBenchmark
% 1.65/0.63  % SZS output start Proof for theBenchmark
% 1.65/0.63  fof(f415,plain,(
% 1.65/0.63    $false),
% 1.65/0.63    inference(avatar_sat_refutation,[],[f101,f157,f178,f211,f267,f277,f287,f300,f306,f331,f345,f372,f393,f407,f413])).
% 1.65/0.63  fof(f413,plain,(
% 1.65/0.63    ~spl8_12 | spl8_14),
% 1.65/0.63    inference(avatar_contradiction_clause,[],[f412])).
% 1.65/0.63  fof(f412,plain,(
% 1.65/0.63    $false | (~spl8_12 | spl8_14)),
% 1.65/0.63    inference(subsumption_resolution,[],[f408,f53])).
% 1.65/0.63  fof(f53,plain,(
% 1.65/0.63    v5_pre_topc(sK7,sK5,sK3)),
% 1.65/0.63    inference(cnf_transformation,[],[f28])).
% 1.65/0.63  fof(f28,plain,(
% 1.65/0.63    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.65/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f27,f26,f25,f24,f23,f22])).
% 1.65/0.63  fof(f22,plain,(
% 1.65/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.65/0.63    introduced(choice_axiom,[])).
% 1.65/0.63  fof(f23,plain,(
% 1.65/0.63    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.65/0.63    introduced(choice_axiom,[])).
% 1.65/0.63  fof(f24,plain,(
% 1.65/0.63    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,sK3,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5))) & r4_tsep_1(sK2,sK4,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 1.65/0.63    introduced(choice_axiom,[])).
% 1.65/0.63  fof(f25,plain,(
% 1.65/0.63    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X3,X4,X5))) & r4_tsep_1(sK2,sK4,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,k10_tmap_1(sK2,sK3,sK4,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.65/0.63    introduced(choice_axiom,[])).
% 1.65/0.63  fof(f26,plain,(
% 1.65/0.63    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(X4,sK4,sK3) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),sK6) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 1.65/0.63    introduced(choice_axiom,[])).
% 2.23/0.65  fof(f27,plain,(
% 2.23/0.65    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X5)),sK6) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(X5,sK5,sK3) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7))),
% 2.23/0.65    introduced(choice_axiom,[])).
% 2.23/0.65  fof(f9,plain,(
% 2.23/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/0.65    inference(flattening,[],[f8])).
% 2.23/0.65  fof(f8,plain,(
% 2.23/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f7])).
% 2.23/0.65  fof(f7,negated_conjecture,(
% 2.23/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.23/0.65    inference(negated_conjecture,[],[f6])).
% 2.23/0.65  fof(f6,conjecture,(
% 2.23/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.23/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).
% 2.23/0.65  fof(f408,plain,(
% 2.23/0.65    ~v5_pre_topc(sK7,sK5,sK3) | (~spl8_12 | spl8_14)),
% 2.23/0.65    inference(backward_demodulation,[],[f392,f210])).
% 2.23/0.65  fof(f210,plain,(
% 2.23/0.65    sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_12),
% 2.23/0.65    inference(avatar_component_clause,[],[f208])).
% 2.23/0.65  fof(f208,plain,(
% 2.23/0.65    spl8_12 <=> sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 2.23/0.65  fof(f392,plain,(
% 2.23/0.65    ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | spl8_14),
% 2.23/0.65    inference(avatar_component_clause,[],[f390])).
% 2.23/0.65  fof(f390,plain,(
% 2.23/0.65    spl8_14 <=> v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 2.23/0.65  fof(f407,plain,(
% 2.23/0.65    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f406])).
% 2.23/0.65  fof(f406,plain,(
% 2.23/0.65    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f405,f36])).
% 2.23/0.65  fof(f36,plain,(
% 2.23/0.65    ~v2_struct_0(sK2)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f405,plain,(
% 2.23/0.65    v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f404,f37])).
% 2.23/0.65  fof(f37,plain,(
% 2.23/0.65    v2_pre_topc(sK2)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f404,plain,(
% 2.23/0.65    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f403,f38])).
% 2.23/0.65  fof(f38,plain,(
% 2.23/0.65    l1_pre_topc(sK2)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f403,plain,(
% 2.23/0.65    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f402,f39])).
% 2.23/0.65  fof(f39,plain,(
% 2.23/0.65    ~v2_struct_0(sK3)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f402,plain,(
% 2.23/0.65    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f401,f40])).
% 2.23/0.65  fof(f40,plain,(
% 2.23/0.65    v2_pre_topc(sK3)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f401,plain,(
% 2.23/0.65    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f400,f41])).
% 2.23/0.65  fof(f41,plain,(
% 2.23/0.65    l1_pre_topc(sK3)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f400,plain,(
% 2.23/0.65    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f399,f104])).
% 2.23/0.65  fof(f104,plain,(
% 2.23/0.65    m1_pre_topc(sK2,sK2)),
% 2.23/0.65    inference(resolution,[],[f38,f82])).
% 2.23/0.65  fof(f82,plain,(
% 2.23/0.65    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f18])).
% 2.23/0.65  fof(f18,plain,(
% 2.23/0.65    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.23/0.65    inference(ennf_transformation,[],[f5])).
% 2.23/0.65  fof(f5,axiom,(
% 2.23/0.65    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.23/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.23/0.65  fof(f399,plain,(
% 2.23/0.65    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f398,f45])).
% 2.23/0.65  fof(f45,plain,(
% 2.23/0.65    m1_pre_topc(sK5,sK2)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f398,plain,(
% 2.23/0.65    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f397,f87])).
% 2.23/0.65  fof(f87,plain,(
% 2.23/0.65    v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_1),
% 2.23/0.65    inference(avatar_component_clause,[],[f86])).
% 2.23/0.65  fof(f86,plain,(
% 2.23/0.65    spl8_1 <=> v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.23/0.65  fof(f397,plain,(
% 2.23/0.65    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f396,f91])).
% 2.23/0.65  fof(f91,plain,(
% 2.23/0.65    v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl8_2),
% 2.23/0.65    inference(avatar_component_clause,[],[f90])).
% 2.23/0.65  fof(f90,plain,(
% 2.23/0.65    spl8_2 <=> v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.23/0.65  fof(f396,plain,(
% 2.23/0.65    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_10)),
% 2.23/0.65    inference(subsumption_resolution,[],[f394,f99])).
% 2.23/0.65  fof(f99,plain,(
% 2.23/0.65    m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~spl8_4),
% 2.23/0.65    inference(avatar_component_clause,[],[f98])).
% 2.23/0.65  fof(f98,plain,(
% 2.23/0.65    spl8_4 <=> m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.23/0.65  fof(f394,plain,(
% 2.23/0.65    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_10),
% 2.23/0.65    inference(resolution,[],[f202,f77])).
% 2.23/0.65  fof(f77,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f15])).
% 2.23/0.65  fof(f15,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.65    inference(flattening,[],[f14])).
% 2.23/0.65  fof(f14,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.65    inference(ennf_transformation,[],[f3])).
% 2.23/0.65  fof(f3,axiom,(
% 2.23/0.65    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.23/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.23/0.65  fof(f202,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | spl8_10),
% 2.23/0.65    inference(avatar_component_clause,[],[f200])).
% 2.23/0.65  fof(f200,plain,(
% 2.23/0.65    spl8_10 <=> v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.23/0.65  fof(f393,plain,(
% 2.23/0.65    ~spl8_11 | ~spl8_14 | ~spl8_10 | spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13),
% 2.23/0.65    inference(avatar_split_clause,[],[f388,f303,f196,f175,f94,f200,f390,f204])).
% 2.23/0.65  fof(f204,plain,(
% 2.23/0.65    spl8_11 <=> m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 2.23/0.65  fof(f94,plain,(
% 2.23/0.65    spl8_3 <=> v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.23/0.65  fof(f175,plain,(
% 2.23/0.65    spl8_8 <=> sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.23/0.65  fof(f196,plain,(
% 2.23/0.65    spl8_9 <=> v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.23/0.65  fof(f303,plain,(
% 2.23/0.65    spl8_13 <=> sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3)),
% 2.23/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 2.23/0.65  fof(f388,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(subsumption_resolution,[],[f387,f47])).
% 2.23/0.65  fof(f47,plain,(
% 2.23/0.65    v1_funct_1(sK6)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f387,plain,(
% 2.23/0.65    ~v1_funct_1(sK6) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f386,f177])).
% 2.23/0.65  fof(f177,plain,(
% 2.23/0.65    sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~spl8_8),
% 2.23/0.65    inference(avatar_component_clause,[],[f175])).
% 2.23/0.65  fof(f386,plain,(
% 2.23/0.65    ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f385,f46])).
% 2.23/0.65  fof(f46,plain,(
% 2.23/0.65    sK2 = k1_tsep_1(sK2,sK4,sK5)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f385,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(subsumption_resolution,[],[f384,f48])).
% 2.23/0.65  fof(f48,plain,(
% 2.23/0.65    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f384,plain,(
% 2.23/0.65    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f383,f177])).
% 2.23/0.65  fof(f383,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f382,f46])).
% 2.23/0.65  fof(f382,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(subsumption_resolution,[],[f381,f49])).
% 2.23/0.65  fof(f49,plain,(
% 2.23/0.65    v5_pre_topc(sK6,sK4,sK3)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f381,plain,(
% 2.23/0.65    ~v5_pre_topc(sK6,sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f380,f177])).
% 2.23/0.65  fof(f380,plain,(
% 2.23/0.65    ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f379,f46])).
% 2.23/0.65  fof(f379,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(subsumption_resolution,[],[f378,f50])).
% 2.23/0.65  fof(f50,plain,(
% 2.23/0.65    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f378,plain,(
% 2.23/0.65    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_8 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f377,f177])).
% 2.23/0.65  fof(f377,plain,(
% 2.23/0.65    ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f376,f46])).
% 2.23/0.65  fof(f376,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_9 | ~spl8_13)),
% 2.23/0.65    inference(subsumption_resolution,[],[f375,f197])).
% 2.23/0.65  fof(f197,plain,(
% 2.23/0.65    v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~spl8_9),
% 2.23/0.65    inference(avatar_component_clause,[],[f196])).
% 2.23/0.65  fof(f375,plain,(
% 2.23/0.65    ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f374,f46])).
% 2.23/0.65  fof(f374,plain,(
% 2.23/0.65    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f373,f46])).
% 2.23/0.65  fof(f373,plain,(
% 2.23/0.65    ~v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f317,f46])).
% 2.23/0.65  fof(f317,plain,(
% 2.23/0.65    ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_13)),
% 2.23/0.65    inference(forward_demodulation,[],[f316,f46])).
% 2.23/0.65  fof(f316,plain,(
% 2.23/0.65    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | (spl8_3 | ~spl8_13)),
% 2.23/0.65    inference(resolution,[],[f310,f72])).
% 2.23/0.65  fof(f72,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 2.23/0.65    inference(cnf_transformation,[],[f34])).
% 2.23/0.65  fof(f34,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.23/0.65    inference(rectify,[],[f33])).
% 2.23/0.65  fof(f33,plain,(
% 2.23/0.65    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 2.23/0.65    inference(flattening,[],[f32])).
% 2.23/0.65  fof(f32,plain,(
% 2.23/0.65    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 2.23/0.65    inference(nnf_transformation,[],[f19])).
% 2.23/0.65  fof(f19,plain,(
% 2.23/0.65    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 2.23/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.23/0.65  fof(f310,plain,(
% 2.23/0.65    ~sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | (spl8_3 | ~spl8_13)),
% 2.23/0.65    inference(subsumption_resolution,[],[f308,f96])).
% 2.23/0.65  fof(f96,plain,(
% 2.23/0.65    ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | spl8_3),
% 2.23/0.65    inference(avatar_component_clause,[],[f94])).
% 2.23/0.65  fof(f308,plain,(
% 2.23/0.65    ~sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~spl8_13),
% 2.23/0.65    inference(resolution,[],[f305,f113])).
% 2.23/0.65  fof(f113,plain,(
% 2.23/0.65    ( ! [X2,X3] : (~sP1(sK2,sK4,X2,sK5,X3) | ~sP0(X3,sK5,X2,sK4,sK2) | v5_pre_topc(X2,sK2,X3)) )),
% 2.23/0.65    inference(superposition,[],[f62,f46])).
% 2.23/0.65  fof(f62,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f31])).
% 2.23/0.65  fof(f31,plain,(
% 2.23/0.65    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 2.23/0.65    inference(rectify,[],[f30])).
% 2.23/0.65  fof(f30,plain,(
% 2.23/0.65    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 2.23/0.65    inference(flattening,[],[f29])).
% 2.23/0.65  fof(f29,plain,(
% 2.23/0.65    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 2.23/0.65    inference(nnf_transformation,[],[f20])).
% 2.23/0.65  fof(f20,plain,(
% 2.23/0.65    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 2.23/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.23/0.65  fof(f305,plain,(
% 2.23/0.65    sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~spl8_13),
% 2.23/0.65    inference(avatar_component_clause,[],[f303])).
% 2.23/0.65  fof(f372,plain,(
% 2.23/0.65    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f371])).
% 2.23/0.65  fof(f371,plain,(
% 2.23/0.65    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f370,f36])).
% 2.23/0.65  fof(f370,plain,(
% 2.23/0.65    v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f369,f37])).
% 2.23/0.65  fof(f369,plain,(
% 2.23/0.65    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f368,f38])).
% 2.23/0.65  fof(f368,plain,(
% 2.23/0.65    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f367,f39])).
% 2.23/0.65  fof(f367,plain,(
% 2.23/0.65    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f366,f40])).
% 2.23/0.65  fof(f366,plain,(
% 2.23/0.65    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f365,f41])).
% 2.23/0.65  fof(f365,plain,(
% 2.23/0.65    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f364,f104])).
% 2.23/0.65  fof(f364,plain,(
% 2.23/0.65    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f363,f45])).
% 2.23/0.65  fof(f363,plain,(
% 2.23/0.65    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f362,f87])).
% 2.23/0.65  fof(f362,plain,(
% 2.23/0.65    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f361,f91])).
% 2.23/0.65  fof(f361,plain,(
% 2.23/0.65    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_11)),
% 2.23/0.65    inference(subsumption_resolution,[],[f359,f99])).
% 2.23/0.65  fof(f359,plain,(
% 2.23/0.65    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_11),
% 2.23/0.65    inference(resolution,[],[f206,f78])).
% 2.23/0.65  fof(f78,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f15])).
% 2.23/0.65  fof(f206,plain,(
% 2.23/0.65    ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_11),
% 2.23/0.65    inference(avatar_component_clause,[],[f204])).
% 2.23/0.65  fof(f345,plain,(
% 2.23/0.65    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7),
% 2.23/0.65    inference(avatar_contradiction_clause,[],[f344])).
% 2.23/0.65  fof(f344,plain,(
% 2.23/0.65    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f343,f36])).
% 2.23/0.65  fof(f343,plain,(
% 2.23/0.65    v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f342,f37])).
% 2.23/0.65  fof(f342,plain,(
% 2.23/0.65    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f341,f38])).
% 2.23/0.65  fof(f341,plain,(
% 2.23/0.65    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f340,f39])).
% 2.23/0.65  fof(f340,plain,(
% 2.23/0.65    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f339,f40])).
% 2.23/0.65  fof(f339,plain,(
% 2.23/0.65    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f338,f41])).
% 2.23/0.65  fof(f338,plain,(
% 2.23/0.65    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f337,f104])).
% 2.23/0.65  fof(f337,plain,(
% 2.23/0.65    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f336,f43])).
% 2.23/0.65  fof(f43,plain,(
% 2.23/0.65    m1_pre_topc(sK4,sK2)),
% 2.23/0.65    inference(cnf_transformation,[],[f28])).
% 2.23/0.65  fof(f336,plain,(
% 2.23/0.65    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f335,f87])).
% 2.23/0.65  fof(f335,plain,(
% 2.23/0.65    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f334,f91])).
% 2.23/0.65  fof(f334,plain,(
% 2.23/0.65    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_7)),
% 2.23/0.65    inference(subsumption_resolution,[],[f332,f99])).
% 2.23/0.65  fof(f332,plain,(
% 2.23/0.65    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_7),
% 2.23/0.65    inference(resolution,[],[f173,f78])).
% 2.23/0.65  fof(f173,plain,(
% 2.23/0.65    ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | spl8_7),
% 2.23/0.65    inference(avatar_component_clause,[],[f171])).
% 2.23/0.66  fof(f171,plain,(
% 2.23/0.66    spl8_7 <=> m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.23/0.66  fof(f331,plain,(
% 2.23/0.66    ~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6),
% 2.23/0.66    inference(avatar_contradiction_clause,[],[f330])).
% 2.23/0.66  fof(f330,plain,(
% 2.23/0.66    $false | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f329,f36])).
% 2.23/0.66  fof(f329,plain,(
% 2.23/0.66    v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f328,f37])).
% 2.23/0.66  fof(f328,plain,(
% 2.23/0.66    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f327,f38])).
% 2.23/0.66  fof(f327,plain,(
% 2.23/0.66    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f326,f39])).
% 2.23/0.66  fof(f326,plain,(
% 2.23/0.66    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f325,f40])).
% 2.23/0.66  fof(f325,plain,(
% 2.23/0.66    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f324,f41])).
% 2.23/0.66  fof(f324,plain,(
% 2.23/0.66    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f323,f104])).
% 2.23/0.66  fof(f323,plain,(
% 2.23/0.66    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f322,f43])).
% 2.23/0.66  fof(f322,plain,(
% 2.23/0.66    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f321,f87])).
% 2.23/0.66  fof(f321,plain,(
% 2.23/0.66    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f320,f91])).
% 2.23/0.66  fof(f320,plain,(
% 2.23/0.66    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_6)),
% 2.23/0.66    inference(subsumption_resolution,[],[f318,f99])).
% 2.23/0.66  fof(f318,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_6),
% 2.23/0.66    inference(resolution,[],[f169,f77])).
% 2.23/0.66  fof(f169,plain,(
% 2.23/0.66    ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | spl8_6),
% 2.23/0.66    inference(avatar_component_clause,[],[f167])).
% 2.23/0.66  fof(f167,plain,(
% 2.23/0.66    spl8_6 <=> v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.23/0.66  fof(f306,plain,(
% 2.23/0.66    spl8_13 | ~spl8_4 | ~spl8_1 | ~spl8_2),
% 2.23/0.66    inference(avatar_split_clause,[],[f301,f90,f86,f98,f303])).
% 2.23/0.66  fof(f301,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | (~spl8_1 | ~spl8_2)),
% 2.23/0.66    inference(subsumption_resolution,[],[f288,f87])).
% 2.23/0.66  fof(f288,plain,(
% 2.23/0.66    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) | ~spl8_2),
% 2.23/0.66    inference(resolution,[],[f91,f227])).
% 2.23/0.66  fof(f227,plain,(
% 2.23/0.66    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP1(sK2,sK4,X1,sK5,sK3)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f226,f39])).
% 2.23/0.66  fof(f226,plain,(
% 2.23/0.66    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v2_struct_0(sK3) | sP1(sK2,sK4,X1,sK5,sK3)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f223,f40])).
% 2.23/0.66  fof(f223,plain,(
% 2.23/0.66    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sP1(sK2,sK4,X1,sK5,sK3)) )),
% 2.23/0.66    inference(resolution,[],[f221,f41])).
% 2.23/0.66  fof(f221,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(forward_demodulation,[],[f220,f46])).
% 2.23/0.66  fof(f220,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(forward_demodulation,[],[f219,f46])).
% 2.23/0.66  fof(f219,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f218,f42])).
% 2.23/0.66  fof(f42,plain,(
% 2.23/0.66    ~v2_struct_0(sK4)),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f218,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f217,f43])).
% 2.23/0.66  fof(f217,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f216,f44])).
% 2.23/0.66  fof(f44,plain,(
% 2.23/0.66    ~v2_struct_0(sK5)),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f216,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f215,f45])).
% 2.23/0.66  fof(f215,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1)))) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(sK2,sK4,X0,sK5,X1)) )),
% 2.23/0.66    inference(resolution,[],[f107,f57])).
% 2.23/0.66  fof(f57,plain,(
% 2.23/0.66    r4_tsep_1(sK2,sK4,sK5)),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f107,plain,(
% 2.23/0.66    ( ! [X2,X0,X3,X1] : (~r4_tsep_1(sK2,X1,X2) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)))) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | sP1(sK2,X1,X0,X2,X3)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f106,f36])).
% 2.23/0.66  fof(f106,plain,(
% 2.23/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK2,X1,X2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | sP1(sK2,X1,X0,X2,X3) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f105,f37])).
% 2.23/0.66  fof(f105,plain,(
% 2.23/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK2,X1,X2) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | sP1(sK2,X1,X0,X2,X3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(resolution,[],[f38,f73])).
% 2.23/0.66  fof(f73,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X0,X2,X4,X3,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f21])).
% 2.23/0.66  fof(f21,plain,(
% 2.23/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.66    inference(definition_folding,[],[f11,f20,f19])).
% 2.23/0.66  fof(f11,plain,(
% 2.23/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.66    inference(flattening,[],[f10])).
% 2.23/0.66  fof(f10,plain,(
% 2.23/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.66    inference(ennf_transformation,[],[f4])).
% 2.23/0.66  fof(f4,axiom,(
% 2.23/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 2.23/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 2.23/0.66  fof(f300,plain,(
% 2.23/0.66    spl8_4),
% 2.23/0.66    inference(avatar_contradiction_clause,[],[f299])).
% 2.23/0.66  fof(f299,plain,(
% 2.23/0.66    $false | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f298,f39])).
% 2.23/0.66  fof(f298,plain,(
% 2.23/0.66    v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f297,f40])).
% 2.23/0.66  fof(f297,plain,(
% 2.23/0.66    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f296,f41])).
% 2.23/0.66  fof(f296,plain,(
% 2.23/0.66    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f295,f47])).
% 2.23/0.66  fof(f295,plain,(
% 2.23/0.66    ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f294,f48])).
% 2.23/0.66  fof(f294,plain,(
% 2.23/0.66    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f293,f50])).
% 2.23/0.66  fof(f293,plain,(
% 2.23/0.66    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f292,f51])).
% 2.23/0.66  fof(f51,plain,(
% 2.23/0.66    v1_funct_1(sK7)),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f292,plain,(
% 2.23/0.66    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f291,f52])).
% 2.23/0.66  fof(f52,plain,(
% 2.23/0.66    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f291,plain,(
% 2.23/0.66    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(subsumption_resolution,[],[f290,f54])).
% 2.23/0.66  fof(f54,plain,(
% 2.23/0.66    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f290,plain,(
% 2.23/0.66    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_4),
% 2.23/0.66    inference(resolution,[],[f138,f100])).
% 2.23/0.66  fof(f100,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | spl8_4),
% 2.23/0.66    inference(avatar_component_clause,[],[f98])).
% 2.23/0.66  fof(f138,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f137,f36])).
% 2.23/0.66  fof(f137,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f136,f37])).
% 2.23/0.66  fof(f136,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f135,f38])).
% 2.23/0.66  fof(f135,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f134,f42])).
% 2.23/0.66  fof(f134,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | v2_struct_0(sK4) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f133,f43])).
% 2.23/0.66  fof(f133,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f132,f44])).
% 2.23/0.66  fof(f132,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f124,f45])).
% 2.23/0.66  fof(f124,plain,(
% 2.23/0.66    ( ! [X26,X27,X25] : (m1_subset_1(k10_tmap_1(sK2,X25,sK4,sK5,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X25)))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X25)))) | ~v1_funct_2(X27,u1_struct_0(sK5),u1_struct_0(X25)) | ~v1_funct_1(X27) | ~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X25)))) | ~v1_funct_2(X26,u1_struct_0(sK4),u1_struct_0(X25)) | ~v1_funct_1(X26) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X25) | ~v2_pre_topc(X25) | v2_struct_0(X25) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(superposition,[],[f81,f46])).
% 2.23/0.66  fof(f81,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f17])).
% 2.23/0.66  fof(f17,plain,(
% 2.23/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.66    inference(flattening,[],[f16])).
% 2.23/0.66  fof(f16,plain,(
% 2.23/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.66    inference(ennf_transformation,[],[f2])).
% 2.23/0.66  fof(f2,axiom,(
% 2.23/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.23/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.23/0.66  fof(f287,plain,(
% 2.23/0.66    ~spl8_2 | ~spl8_4 | ~spl8_1 | spl8_5),
% 2.23/0.66    inference(avatar_split_clause,[],[f286,f163,f86,f98,f90])).
% 2.23/0.66  fof(f163,plain,(
% 2.23/0.66    spl8_5 <=> v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.23/0.66  fof(f286,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f285,f36])).
% 2.23/0.66  fof(f285,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f284,f37])).
% 2.23/0.66  fof(f284,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f283,f38])).
% 2.23/0.66  fof(f283,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f282,f39])).
% 2.23/0.66  fof(f282,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f281,f40])).
% 2.23/0.66  fof(f281,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f280,f41])).
% 2.23/0.66  fof(f280,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f279,f104])).
% 2.23/0.66  fof(f279,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f278,f43])).
% 2.23/0.66  fof(f278,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_5)),
% 2.23/0.66    inference(subsumption_resolution,[],[f180,f87])).
% 2.23/0.66  fof(f180,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_5),
% 2.23/0.66    inference(resolution,[],[f165,f76])).
% 2.23/0.66  fof(f76,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f15])).
% 2.23/0.66  fof(f165,plain,(
% 2.23/0.66    ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | spl8_5),
% 2.23/0.66    inference(avatar_component_clause,[],[f163])).
% 2.23/0.66  fof(f277,plain,(
% 2.23/0.66    ~spl8_2 | ~spl8_4 | ~spl8_1 | spl8_9),
% 2.23/0.66    inference(avatar_split_clause,[],[f276,f196,f86,f98,f90])).
% 2.23/0.66  fof(f276,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f275,f36])).
% 2.23/0.66  fof(f275,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f274,f37])).
% 2.23/0.66  fof(f274,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f273,f38])).
% 2.23/0.66  fof(f273,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f272,f39])).
% 2.23/0.66  fof(f272,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f271,f40])).
% 2.23/0.66  fof(f271,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f270,f41])).
% 2.23/0.66  fof(f270,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f269,f104])).
% 2.23/0.66  fof(f269,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f268,f45])).
% 2.23/0.66  fof(f268,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_1 | spl8_9)),
% 2.23/0.66    inference(subsumption_resolution,[],[f213,f87])).
% 2.23/0.66  fof(f213,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_9),
% 2.23/0.66    inference(resolution,[],[f198,f76])).
% 2.23/0.66  fof(f198,plain,(
% 2.23/0.66    ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) | spl8_9),
% 2.23/0.66    inference(avatar_component_clause,[],[f196])).
% 2.23/0.66  fof(f267,plain,(
% 2.23/0.66    spl8_2),
% 2.23/0.66    inference(avatar_contradiction_clause,[],[f266])).
% 2.23/0.66  fof(f266,plain,(
% 2.23/0.66    $false | spl8_2),
% 2.23/0.66    inference(subsumption_resolution,[],[f265,f54])).
% 2.23/0.66  fof(f265,plain,(
% 2.23/0.66    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_2),
% 2.23/0.66    inference(subsumption_resolution,[],[f264,f47])).
% 2.23/0.66  fof(f264,plain,(
% 2.23/0.66    ~v1_funct_1(sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_2),
% 2.23/0.66    inference(subsumption_resolution,[],[f263,f48])).
% 2.23/0.66  fof(f263,plain,(
% 2.23/0.66    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_2),
% 2.23/0.66    inference(subsumption_resolution,[],[f262,f50])).
% 2.23/0.66  fof(f262,plain,(
% 2.23/0.66    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_2),
% 2.23/0.66    inference(subsumption_resolution,[],[f261,f51])).
% 2.23/0.66  fof(f261,plain,(
% 2.23/0.66    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_2),
% 2.23/0.66    inference(subsumption_resolution,[],[f259,f52])).
% 2.23/0.66  fof(f259,plain,(
% 2.23/0.66    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl8_2),
% 2.23/0.66    inference(resolution,[],[f257,f92])).
% 2.23/0.66  fof(f92,plain,(
% 2.23/0.66    ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | spl8_2),
% 2.23/0.66    inference(avatar_component_clause,[],[f90])).
% 2.23/0.66  fof(f257,plain,(
% 2.23/0.66    ( ! [X2,X3] : (v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X3,X2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f256,f39])).
% 2.23/0.66  fof(f256,plain,(
% 2.23/0.66    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X3) | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X3,X2),u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f253,f40])).
% 2.23/0.66  fof(f253,plain,(
% 2.23/0.66    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X3) | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X3,X2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.23/0.66    inference(resolution,[],[f131,f41])).
% 2.23/0.66  fof(f131,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (~l1_pre_topc(X22) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~v2_pre_topc(X22) | v2_struct_0(X22)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f130,f36])).
% 2.23/0.66  fof(f130,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f129,f37])).
% 2.23/0.66  fof(f129,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f128,f38])).
% 2.23/0.66  fof(f128,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f127,f42])).
% 2.23/0.66  fof(f127,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | v2_struct_0(sK4) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f126,f43])).
% 2.23/0.66  fof(f126,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f125,f44])).
% 2.23/0.66  fof(f125,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f123,f45])).
% 2.23/0.66  fof(f123,plain,(
% 2.23/0.66    ( ! [X24,X23,X22] : (v1_funct_2(k10_tmap_1(sK2,X22,sK4,sK5,X23,X24),u1_struct_0(sK2),u1_struct_0(X22)) | ~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X22)))) | ~v1_funct_2(X24,u1_struct_0(sK5),u1_struct_0(X22)) | ~v1_funct_1(X24) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK4),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X22) | ~v2_pre_topc(X22) | v2_struct_0(X22) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.66    inference(superposition,[],[f80,f46])).
% 2.23/0.66  fof(f80,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f17])).
% 2.23/0.66  fof(f211,plain,(
% 2.23/0.66    ~spl8_9 | ~spl8_10 | ~spl8_11 | spl8_12),
% 2.23/0.66    inference(avatar_split_clause,[],[f194,f208,f204,f200,f196])).
% 2.23/0.66  fof(f194,plain,(
% 2.23/0.66    sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f193,f51])).
% 2.23/0.66  fof(f193,plain,(
% 2.23/0.66    sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_1(sK7) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f192,f52])).
% 2.23/0.66  fof(f192,plain,(
% 2.23/0.66    sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f191,f54])).
% 2.23/0.66  fof(f191,plain,(
% 2.23/0.66    sK7 = k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(resolution,[],[f103,f74])).
% 2.23/0.66  fof(f74,plain,(
% 2.23/0.66    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f35])).
% 2.23/0.66  fof(f35,plain,(
% 2.23/0.66    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.66    inference(nnf_transformation,[],[f13])).
% 2.23/0.66  fof(f13,plain,(
% 2.23/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.66    inference(flattening,[],[f12])).
% 2.23/0.66  fof(f12,plain,(
% 2.23/0.66    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.23/0.66    inference(ennf_transformation,[],[f1])).
% 2.23/0.66  fof(f1,axiom,(
% 2.23/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.23/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.23/0.66  fof(f103,plain,(
% 2.23/0.66    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 2.23/0.66    inference(backward_demodulation,[],[f56,f46])).
% 2.23/0.66  fof(f56,plain,(
% 2.23/0.66    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f178,plain,(
% 2.23/0.66    ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 2.23/0.66    inference(avatar_split_clause,[],[f161,f175,f171,f167,f163])).
% 2.23/0.66  fof(f161,plain,(
% 2.23/0.66    sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f160,f47])).
% 2.23/0.66  fof(f160,plain,(
% 2.23/0.66    sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f159,f48])).
% 2.23/0.66  fof(f159,plain,(
% 2.23/0.66    sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f158,f50])).
% 2.23/0.66  fof(f158,plain,(
% 2.23/0.66    sK6 = k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))),
% 2.23/0.66    inference(resolution,[],[f102,f74])).
% 2.23/0.66  fof(f102,plain,(
% 2.23/0.66    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 2.23/0.66    inference(backward_demodulation,[],[f55,f46])).
% 2.23/0.66  fof(f55,plain,(
% 2.23/0.66    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  fof(f157,plain,(
% 2.23/0.66    spl8_1),
% 2.23/0.66    inference(avatar_contradiction_clause,[],[f156])).
% 2.23/0.66  fof(f156,plain,(
% 2.23/0.66    $false | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f155,f36])).
% 2.23/0.66  fof(f155,plain,(
% 2.23/0.66    v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f154,f37])).
% 2.23/0.66  fof(f154,plain,(
% 2.23/0.66    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f153,f38])).
% 2.23/0.66  fof(f153,plain,(
% 2.23/0.66    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f152,f39])).
% 2.23/0.66  fof(f152,plain,(
% 2.23/0.66    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f151,f40])).
% 2.23/0.66  fof(f151,plain,(
% 2.23/0.66    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f150,f41])).
% 2.23/0.66  fof(f150,plain,(
% 2.23/0.66    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f149,f42])).
% 2.23/0.66  fof(f149,plain,(
% 2.23/0.66    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f148,f43])).
% 2.23/0.66  fof(f148,plain,(
% 2.23/0.66    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f147,f44])).
% 2.23/0.66  fof(f147,plain,(
% 2.23/0.66    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f146,f45])).
% 2.23/0.66  fof(f146,plain,(
% 2.23/0.66    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f145,f47])).
% 2.23/0.66  fof(f145,plain,(
% 2.23/0.66    ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f144,f48])).
% 2.23/0.66  fof(f144,plain,(
% 2.23/0.66    ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f143,f50])).
% 2.23/0.66  fof(f143,plain,(
% 2.23/0.66    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f142,f51])).
% 2.23/0.66  fof(f142,plain,(
% 2.23/0.66    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f141,f52])).
% 2.23/0.66  fof(f141,plain,(
% 2.23/0.66    ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(subsumption_resolution,[],[f139,f54])).
% 2.23/0.66  fof(f139,plain,(
% 2.23/0.66    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl8_1),
% 2.23/0.66    inference(resolution,[],[f88,f79])).
% 2.23/0.66  fof(f79,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f17])).
% 2.23/0.66  fof(f88,plain,(
% 2.23/0.66    ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_1),
% 2.23/0.66    inference(avatar_component_clause,[],[f86])).
% 2.23/0.66  fof(f101,plain,(
% 2.23/0.66    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 2.23/0.66    inference(avatar_split_clause,[],[f58,f98,f94,f90,f86])).
% 2.23/0.66  fof(f58,plain,(
% 2.23/0.66    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.23/0.66    inference(cnf_transformation,[],[f28])).
% 2.23/0.66  % SZS output end Proof for theBenchmark
% 2.23/0.66  % (28104)------------------------------
% 2.23/0.66  % (28104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.66  % (28104)Termination reason: Refutation
% 2.23/0.66  
% 2.23/0.66  % (28104)Memory used [KB]: 11129
% 2.23/0.66  % (28104)Time elapsed: 0.209 s
% 2.23/0.66  % (28104)------------------------------
% 2.23/0.66  % (28104)------------------------------
% 2.23/0.67  % (28097)Success in time 0.304 s
%------------------------------------------------------------------------------

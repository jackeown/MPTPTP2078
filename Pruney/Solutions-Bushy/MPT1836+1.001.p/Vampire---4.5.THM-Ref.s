%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1836+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:42 EST 2020

% Result     : Theorem 3.98s
% Output     : Refutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  398 (2709 expanded)
%              Number of leaves         :   43 (1308 expanded)
%              Depth                    :   45
%              Number of atoms          : 2865 (65570 expanded)
%              Number of equality atoms :  102 (2951 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f228,f233,f391,f394,f397,f427,f780,f789,f1448,f1463,f1511,f1602,f1713,f1991,f2008,f2013,f2019,f2027,f2444,f3254])).

fof(f3254,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_35
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f3253])).

fof(f3253,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_35
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3252,f1756])).

fof(f1756,plain,
    ( sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f1755,plain,
    ( spl11_35
  <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f3252,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3251,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f16,f53,f52,f51,f50,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f52,plain,
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

fof(f53,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f3251,plain,
    ( v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3250,f73])).

fof(f73,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f3250,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3249,f74])).

fof(f74,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f3249,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | spl11_23
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3248,f1545])).

fof(f1545,plain,
    ( ~ sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | spl11_23 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1544,plain,
    ( spl11_23
  <=> sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f3248,plain,
    ( sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3247,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f3247,plain,
    ( v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3246,f76])).

fof(f76,plain,(
    v1_borsuk_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f3246,plain,
    ( ~ v1_borsuk_1(sK7,sK5)
    | v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3245,f77])).

fof(f77,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f3245,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ v1_borsuk_1(sK7,sK5)
    | v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3244,f78])).

fof(f78,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f3244,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_borsuk_1(sK7,sK5)
    | v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3243,f79])).

fof(f79,plain,(
    v1_borsuk_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f3243,plain,
    ( ~ v1_borsuk_1(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_borsuk_1(sK7,sK5)
    | v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3242,f80])).

fof(f80,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f3242,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ v1_borsuk_1(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_borsuk_1(sK7,sK5)
    | v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3231,f89])).

fof(f89,plain,(
    sK5 = k1_tsep_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f3231,plain,
    ( sK5 != k1_tsep_1(sK5,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ v1_borsuk_1(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_borsuk_1(sK7,sK5)
    | v2_struct_0(sK7)
    | sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(resolution,[],[f3200,f629])).

fof(f629,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),sK5,X4)
      | sK5 != k1_tsep_1(sK5,X4,X1)
      | ~ m1_pre_topc(X1,sK5)
      | ~ v1_borsuk_1(X1,sK5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,sK5)
      | ~ v1_borsuk_1(X4,sK5)
      | v2_struct_0(X4)
      | sP0(X0,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X3,X2) ) ),
    inference(subsumption_resolution,[],[f628,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP4(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP4(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f628,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),sK5,X4)
      | sK5 != k1_tsep_1(sK5,X4,X1)
      | ~ m1_pre_topc(X1,sK5)
      | ~ v1_borsuk_1(X1,sK5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,sK5)
      | ~ v1_borsuk_1(X4,sK5)
      | v2_struct_0(X4)
      | sP0(X0,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X3,X2) ) ),
    inference(subsumption_resolution,[],[f627,f247])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f128,f89])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f627,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),sK5,X4)
      | sK5 != k1_tsep_1(sK5,X4,X1)
      | ~ m1_pre_topc(X1,sK5)
      | ~ v1_borsuk_1(X1,sK5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,sK5)
      | ~ v1_borsuk_1(X4,sK5)
      | v2_struct_0(X4)
      | sP0(X0,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0,sK8,sK7,sK5,X3,X2) ) ),
    inference(subsumption_resolution,[],[f626,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f626,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),sK5,X4)
      | sK5 != k1_tsep_1(sK5,X4,X1)
      | ~ m1_pre_topc(X1,sK5)
      | ~ v1_borsuk_1(X1,sK5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,sK5)
      | ~ v1_borsuk_1(X4,sK5)
      | v2_struct_0(X4)
      | sP0(X0,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK5)
      | ~ sP4(X0,sK8,sK7,sK5,X3,X2) ) ),
    inference(subsumption_resolution,[],[f625,f70])).

fof(f70,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f625,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),sK5,X4)
      | sK5 != k1_tsep_1(sK5,X4,X1)
      | ~ m1_pre_topc(X1,sK5)
      | ~ v1_borsuk_1(X1,sK5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,sK5)
      | ~ v1_borsuk_1(X4,sK5)
      | v2_struct_0(X4)
      | sP0(X0,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ sP4(X0,sK8,sK7,sK5,X3,X2) ) ),
    inference(subsumption_resolution,[],[f615,f71])).

fof(f71,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f615,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),sK5,X4)
      | sK5 != k1_tsep_1(sK5,X4,X1)
      | ~ m1_pre_topc(X1,sK5)
      | ~ v1_borsuk_1(X1,sK5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,sK5)
      | ~ v1_borsuk_1(X4,sK5)
      | v2_struct_0(X4)
      | sP0(X0,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ sP4(X0,sK8,sK7,sK5,X3,X2) ) ),
    inference(resolution,[],[f112,f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f129,f89])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ sP1(X1,X4,X2,X0,X3)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | ~ v1_borsuk_1(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_borsuk_1(X3,X0)
      | v2_struct_0(X3)
      | sP0(X1,X0,X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( sP0(X1,X0,X2)
                          | ~ sP1(X1,X4,X2,X0,X3) )
                        & ( sP1(X1,X4,X2,X0,X3)
                          | ~ sP0(X1,X0,X2) ) )
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( sP0(X1,X0,X2)
                      <=> sP1(X1,X4,X2,X0,X3) )
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(definition_folding,[],[f24,f40,f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f40,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP1(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
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
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f3200,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK7)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3197,f270])).

fof(f270,plain,(
    sP0(sK6,sK7,sK9) ),
    inference(subsumption_resolution,[],[f269,f81])).

fof(f81,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f54])).

fof(f269,plain,
    ( sP0(sK6,sK7,sK9)
    | ~ v1_funct_1(sK9) ),
    inference(subsumption_resolution,[],[f268,f82])).

fof(f82,plain,(
    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f268,plain,
    ( sP0(sK6,sK7,sK9)
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(sK9) ),
    inference(subsumption_resolution,[],[f260,f83])).

fof(f83,plain,(
    v5_pre_topc(sK9,sK7,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f260,plain,
    ( sP0(sK6,sK7,sK9)
    | ~ v5_pre_topc(sK9,sK7,sK6)
    | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(sK9) ),
    inference(resolution,[],[f110,f84])).

fof(f84,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP0(X0,X1,X2)
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X1,X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f3197,plain,
    ( ~ sP0(sK6,sK7,sK9)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK7)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16
    | ~ spl11_50 ),
    inference(superposition,[],[f2896,f2303])).

fof(f2303,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2302,f69])).

fof(f2302,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2301,f70])).

fof(f2301,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2300,f71])).

fof(f2300,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2299,f72])).

fof(f2299,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2298,f73])).

fof(f2298,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2297,f74])).

fof(f2297,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2296,f232])).

fof(f232,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl11_7
  <=> m1_pre_topc(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f2296,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2295,f135])).

fof(f135,plain,
    ( v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl11_1
  <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f2295,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2294,f139])).

fof(f139,plain,
    ( v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_2
  <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2294,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_4
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2293,f147])).

fof(f147,plain,
    ( m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl11_4
  <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f2293,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f2290,f77])).

fof(f2290,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_16 ),
    inference(duplicate_literal_removal,[],[f2253])).

fof(f2253,plain,
    ( sK9 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_16 ),
    inference(superposition,[],[f541,f513])).

fof(f513,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f511])).

fof(f511,plain,
    ( spl11_16
  <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f541,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f540,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f540,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f538,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f538,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f516])).

fof(f516,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f95,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f2896,plain,
    ( ! [X6] :
        ( ~ sP0(sK6,X6,k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6))
        | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,X6) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f2895,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2895,plain,
    ( ! [X6] :
        ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,X6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6),u1_struct_0(X6),u1_struct_0(sK6))
        | ~ sP0(sK6,X6,k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f2894,f85])).

fof(f85,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f54])).

fof(f2894,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(sK10)
        | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,X6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6),u1_struct_0(X6),u1_struct_0(sK6))
        | ~ sP0(sK6,X6,k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f2893,f86])).

fof(f86,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f2893,plain,
    ( ! [X6] :
        ( ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(sK10)
        | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,X6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6),u1_struct_0(X6),u1_struct_0(sK6))
        | ~ sP0(sK6,X6,k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f2892,f87])).

fof(f87,plain,(
    v5_pre_topc(sK10,sK8,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f2892,plain,
    ( ! [X6] :
        ( ~ v5_pre_topc(sK10,sK8,sK6)
        | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(sK10)
        | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,X6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6),u1_struct_0(X6),u1_struct_0(sK6))
        | ~ sP0(sK6,X6,k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f2871,f88])).

fof(f88,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f2871,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v5_pre_topc(sK10,sK8,sK6)
        | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(sK10)
        | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,X6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6),u1_struct_0(X6),u1_struct_0(sK6))
        | ~ sP0(sK6,X6,k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X6)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(superposition,[],[f742,f2483])).

fof(f2483,plain,
    ( sK10 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f2476,f2433])).

fof(f2433,plain,
    ( sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f2432])).

fof(f2432,plain,
    ( spl11_50
  <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f2476,plain,
    ( sK10 = k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8)
    | ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(resolution,[],[f2325,f590])).

fof(f590,plain,(
    ! [X6,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(X6,sK6,X7,sK8),sK10)
      | sK10 = k2_tmap_1(X6,sK6,X7,sK8)
      | ~ sP3(sK6,sK8,X7,X6) ) ),
    inference(subsumption_resolution,[],[f589,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP3(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP3(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f589,plain,(
    ! [X6,X7] :
      ( sK10 = k2_tmap_1(X6,sK6,X7,sK8)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(X6,sK6,X7,sK8),sK10)
      | ~ v1_funct_1(k2_tmap_1(X6,sK6,X7,sK8))
      | ~ sP3(sK6,sK8,X7,X6) ) ),
    inference(subsumption_resolution,[],[f581,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f581,plain,(
    ! [X6,X7] :
      ( sK10 = k2_tmap_1(X6,sK6,X7,sK8)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(X6,sK6,X7,sK8),sK10)
      | ~ v1_funct_2(k2_tmap_1(X6,sK6,X7,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(k2_tmap_1(X6,sK6,X7,sK8))
      | ~ sP3(sK6,sK8,X7,X6) ) ),
    inference(resolution,[],[f423,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f423,plain,(
    ! [X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | sK10 = X33
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X33,sK10)
      | ~ v1_funct_2(X33,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X33) ) ),
    inference(subsumption_resolution,[],[f422,f85])).

fof(f422,plain,(
    ! [X33] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X33,sK10)
      | sK10 = X33
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X33,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X33) ) ),
    inference(subsumption_resolution,[],[f405,f86])).

fof(f405,plain,(
    ! [X33] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X33,sK10)
      | sK10 = X33
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X33,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X33) ) ),
    inference(resolution,[],[f122,f88])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f2325,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2324,f69])).

fof(f2324,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2323,f70])).

fof(f2323,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2322,f71])).

fof(f2322,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2321,f72])).

fof(f2321,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2320,f73])).

fof(f2320,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2319,f74])).

fof(f2319,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2318,f232])).

fof(f2318,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2317,f135])).

fof(f2317,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2316,f139])).

fof(f2316,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2315,f147])).

fof(f2315,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f2288,f80])).

fof(f2288,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(duplicate_literal_removal,[],[f2255])).

fof(f2255,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k2_tmap_1(sK5,sK6,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK8),sK10)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK5) ),
    inference(superposition,[],[f155,f541])).

fof(f155,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(forward_demodulation,[],[f91,f89])).

fof(f91,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(cnf_transformation,[],[f54])).

fof(f742,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( ~ m1_subset_1(k2_tmap_1(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X18))))
      | ~ v5_pre_topc(k2_tmap_1(X17,X18,X19,X20),X20,X18)
      | ~ v1_funct_2(k2_tmap_1(X17,X18,X19,X20),u1_struct_0(X20),u1_struct_0(X18))
      | ~ v1_funct_1(k2_tmap_1(X17,X18,X19,X20))
      | sP1(X18,X20,X19,X17,X21)
      | ~ v1_funct_2(k2_tmap_1(X17,X18,X19,X21),u1_struct_0(X21),u1_struct_0(X18))
      | ~ sP0(X18,X21,k2_tmap_1(X17,X18,X19,X21)) ) ),
    inference(subsumption_resolution,[],[f741,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f741,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( ~ m1_subset_1(k2_tmap_1(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X18))))
      | ~ v5_pre_topc(k2_tmap_1(X17,X18,X19,X20),X20,X18)
      | ~ v1_funct_2(k2_tmap_1(X17,X18,X19,X20),u1_struct_0(X20),u1_struct_0(X18))
      | ~ v1_funct_1(k2_tmap_1(X17,X18,X19,X20))
      | sP1(X18,X20,X19,X17,X21)
      | ~ v5_pre_topc(k2_tmap_1(X17,X18,X19,X21),X21,X18)
      | ~ v1_funct_2(k2_tmap_1(X17,X18,X19,X21),u1_struct_0(X21),u1_struct_0(X18))
      | ~ sP0(X18,X21,k2_tmap_1(X17,X18,X19,X21)) ) ),
    inference(subsumption_resolution,[],[f740,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f740,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( ~ m1_subset_1(k2_tmap_1(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X18))))
      | ~ v5_pre_topc(k2_tmap_1(X17,X18,X19,X20),X20,X18)
      | ~ v1_funct_2(k2_tmap_1(X17,X18,X19,X20),u1_struct_0(X20),u1_struct_0(X18))
      | ~ v1_funct_1(k2_tmap_1(X17,X18,X19,X20))
      | sP1(X18,X20,X19,X17,X21)
      | ~ v5_pre_topc(k2_tmap_1(X17,X18,X19,X21),X21,X18)
      | ~ v1_funct_2(k2_tmap_1(X17,X18,X19,X21),u1_struct_0(X21),u1_struct_0(X18))
      | ~ v1_funct_1(k2_tmap_1(X17,X18,X19,X21))
      | ~ sP0(X18,X21,k2_tmap_1(X17,X18,X19,X21)) ) ),
    inference(resolution,[],[f105,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | sP1(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
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
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP1(X1,X4,X2,X0,X3)
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
        | ~ sP1(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP1(X1,X4,X2,X0,X3)
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
        | ~ sP1(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f2444,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_13
    | spl11_50 ),
    inference(avatar_contradiction_clause,[],[f2443])).

fof(f2443,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_13
    | spl11_50 ),
    inference(subsumption_resolution,[],[f2440,f382])).

fof(f382,plain,
    ( l1_struct_0(sK8)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl11_13
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f2440,plain,
    ( ~ l1_struct_0(sK8)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_11
    | spl11_50 ),
    inference(resolution,[],[f2434,f1554])).

fof(f1554,plain,
    ( ! [X4] :
        ( sP3(sK6,X4,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
        | ~ l1_struct_0(X4) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f1553,f348])).

fof(f348,plain,
    ( l1_struct_0(sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl11_8
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1553,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | sP3(sK6,X4,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f1552,f372])).

fof(f372,plain,
    ( l1_struct_0(sK6)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl11_11
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f1552,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | sP3(sK6,X4,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
        | ~ l1_struct_0(sK6)
        | ~ l1_struct_0(sK5) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1551,f135])).

fof(f1551,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | sP3(sK6,X4,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
        | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
        | ~ l1_struct_0(sK6)
        | ~ l1_struct_0(sK5) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1516,f139])).

fof(f1516,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | sP3(sK6,X4,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
        | ~ l1_struct_0(sK6)
        | ~ l1_struct_0(sK5) )
    | ~ spl11_4 ),
    inference(resolution,[],[f147,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP3(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f30,f44])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f2434,plain,
    ( ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
    | spl11_50 ),
    inference(avatar_component_clause,[],[f2432])).

fof(f2027,plain,
    ( spl11_28
    | spl11_26
    | ~ spl11_1
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f2026,f1460,f134,f1637,f1648])).

fof(f1648,plain,
    ( spl11_28
  <=> ! [X4] :
        ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(X4),u1_struct_0(sK6))
        | ~ m1_pre_topc(sK7,X4)
        | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f1637,plain,
    ( spl11_26
  <=> sK9 = k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f1460,plain,
    ( spl11_20
  <=> r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f2026,plain,
    ( ! [X4] :
        ( sK9 = k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7))
        | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X4)
        | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6))))
        | ~ m1_pre_topc(sK7,X4)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(X4),u1_struct_0(sK6))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl11_1
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f1781,f135])).

fof(f1781,plain,
    ( ! [X4] :
        ( sK9 = k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7))
        | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X4)
        | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6))))
        | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
        | ~ m1_pre_topc(sK7,X4)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(X4),u1_struct_0(sK6))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl11_20 ),
    inference(resolution,[],[f1462,f1132])).

fof(f1132,plain,(
    ! [X255,X256] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(X256,u1_struct_0(sK7)),sK9)
      | sK9 = k7_relat_1(X256,u1_struct_0(sK7))
      | ~ sP3(sK6,sK7,X256,X255)
      | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X255),u1_struct_0(sK6))))
      | ~ v1_funct_1(X256)
      | ~ m1_pre_topc(sK7,X255)
      | ~ v1_funct_2(X256,u1_struct_0(X255),u1_struct_0(sK6))
      | ~ l1_pre_topc(X255)
      | ~ v2_pre_topc(X255)
      | v2_struct_0(X255) ) ),
    inference(subsumption_resolution,[],[f1131,f72])).

fof(f1131,plain,(
    ! [X255,X256] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(X256,u1_struct_0(sK7)),sK9)
      | sK9 = k7_relat_1(X256,u1_struct_0(sK7))
      | ~ sP3(sK6,sK7,X256,X255)
      | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X255),u1_struct_0(sK6))))
      | ~ v1_funct_1(X256)
      | ~ m1_pre_topc(sK7,X255)
      | ~ v1_funct_2(X256,u1_struct_0(X255),u1_struct_0(sK6))
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X255)
      | ~ v2_pre_topc(X255)
      | v2_struct_0(X255) ) ),
    inference(subsumption_resolution,[],[f1130,f73])).

fof(f1130,plain,(
    ! [X255,X256] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(X256,u1_struct_0(sK7)),sK9)
      | sK9 = k7_relat_1(X256,u1_struct_0(sK7))
      | ~ sP3(sK6,sK7,X256,X255)
      | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X255),u1_struct_0(sK6))))
      | ~ v1_funct_1(X256)
      | ~ m1_pre_topc(sK7,X255)
      | ~ v1_funct_2(X256,u1_struct_0(X255),u1_struct_0(sK6))
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X255)
      | ~ v2_pre_topc(X255)
      | v2_struct_0(X255) ) ),
    inference(subsumption_resolution,[],[f1080,f74])).

fof(f1080,plain,(
    ! [X255,X256] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(X256,u1_struct_0(sK7)),sK9)
      | sK9 = k7_relat_1(X256,u1_struct_0(sK7))
      | ~ sP3(sK6,sK7,X256,X255)
      | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X255),u1_struct_0(sK6))))
      | ~ v1_funct_1(X256)
      | ~ m1_pre_topc(sK7,X255)
      | ~ v1_funct_2(X256,u1_struct_0(X255),u1_struct_0(sK6))
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X255)
      | ~ v2_pre_topc(X255)
      | v2_struct_0(X255) ) ),
    inference(superposition,[],[f440,f458])).

fof(f458,plain,(
    ! [X43,X41,X44,X42] :
      ( k2_tmap_1(X41,X42,X43,X44) = k7_relat_1(X43,u1_struct_0(X44))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
      | ~ v1_funct_1(X43)
      | ~ m1_pre_topc(X44,X41)
      | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
      | ~ l1_pre_topc(X42)
      | ~ v2_pre_topc(X42)
      | v2_struct_0(X42)
      | ~ l1_pre_topc(X41)
      | ~ v2_pre_topc(X41)
      | v2_struct_0(X41) ) ),
    inference(duplicate_literal_removal,[],[f455])).

fof(f455,plain,(
    ! [X43,X41,X44,X42] :
      ( k2_tmap_1(X41,X42,X43,X44) = k7_relat_1(X43,u1_struct_0(X44))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
      | ~ v1_funct_1(X43)
      | ~ m1_pre_topc(X44,X41)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
      | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
      | ~ v1_funct_1(X43)
      | ~ l1_pre_topc(X42)
      | ~ v2_pre_topc(X42)
      | v2_struct_0(X42)
      | ~ l1_pre_topc(X41)
      | ~ v2_pre_topc(X41)
      | v2_struct_0(X41) ) ),
    inference(superposition,[],[f124,f96])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f440,plain,(
    ! [X6,X7] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tmap_1(X6,sK6,X7,sK7),sK9)
      | sK9 = k2_tmap_1(X6,sK6,X7,sK7)
      | ~ sP3(sK6,sK7,X7,X6) ) ),
    inference(subsumption_resolution,[],[f439,f118])).

fof(f439,plain,(
    ! [X6,X7] :
      ( sK9 = k2_tmap_1(X6,sK6,X7,sK7)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tmap_1(X6,sK6,X7,sK7),sK9)
      | ~ v1_funct_1(k2_tmap_1(X6,sK6,X7,sK7))
      | ~ sP3(sK6,sK7,X7,X6) ) ),
    inference(subsumption_resolution,[],[f431,f119])).

fof(f431,plain,(
    ! [X6,X7] :
      ( sK9 = k2_tmap_1(X6,sK6,X7,sK7)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k2_tmap_1(X6,sK6,X7,sK7),sK9)
      | ~ v1_funct_2(k2_tmap_1(X6,sK6,X7,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(k2_tmap_1(X6,sK6,X7,sK7))
      | ~ sP3(sK6,sK7,X7,X6) ) ),
    inference(resolution,[],[f421,f120])).

fof(f421,plain,(
    ! [X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | sK9 = X32
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X32,sK9)
      | ~ v1_funct_2(X32,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X32) ) ),
    inference(subsumption_resolution,[],[f420,f81])).

fof(f420,plain,(
    ! [X32] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X32,sK9)
      | sK9 = X32
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X32,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X32) ) ),
    inference(subsumption_resolution,[],[f404,f82])).

fof(f404,plain,(
    ! [X32] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X32,sK9)
      | sK9 = X32
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X32,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X32) ) ),
    inference(resolution,[],[f122,f84])).

fof(f1462,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f1460])).

fof(f2019,plain,
    ( ~ spl11_15
    | spl11_16 ),
    inference(avatar_split_clause,[],[f2018,f511,f507])).

fof(f507,plain,
    ( spl11_15
  <=> sP0(sK6,sK7,k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f2018,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP0(sK6,sK7,k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) ),
    inference(subsumption_resolution,[],[f906,f270])).

fof(f906,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP0(sK6,sK7,sK9)
    | ~ sP0(sK6,sK7,k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) ),
    inference(resolution,[],[f880,f154])).

fof(f154,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(forward_demodulation,[],[f90,f89])).

fof(f90,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(cnf_transformation,[],[f54])).

fof(f880,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ r2_funct_2(u1_struct_0(X30),u1_struct_0(X31),X28,X29)
      | X28 = X29
      | ~ sP0(X31,X30,X29)
      | ~ sP0(X31,X30,X28) ) ),
    inference(subsumption_resolution,[],[f879,f107])).

fof(f879,plain,(
    ! [X30,X28,X31,X29] :
      ( X28 = X29
      | ~ r2_funct_2(u1_struct_0(X30),u1_struct_0(X31),X28,X29)
      | ~ v1_funct_2(X28,u1_struct_0(X30),u1_struct_0(X31))
      | ~ sP0(X31,X30,X29)
      | ~ sP0(X31,X30,X28) ) ),
    inference(subsumption_resolution,[],[f864,f106])).

fof(f864,plain,(
    ! [X30,X28,X31,X29] :
      ( X28 = X29
      | ~ r2_funct_2(u1_struct_0(X30),u1_struct_0(X31),X28,X29)
      | ~ v1_funct_2(X28,u1_struct_0(X30),u1_struct_0(X31))
      | ~ v1_funct_1(X28)
      | ~ sP0(X31,X30,X29)
      | ~ sP0(X31,X30,X28) ) ),
    inference(resolution,[],[f419,f109])).

fof(f419,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | X30 = X31
      | ~ r2_funct_2(u1_struct_0(X28),u1_struct_0(X29),X30,X31)
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
      | ~ v1_funct_1(X30)
      | ~ sP0(X29,X28,X31) ) ),
    inference(subsumption_resolution,[],[f418,f107])).

fof(f418,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ r2_funct_2(u1_struct_0(X28),u1_struct_0(X29),X30,X31)
      | X30 = X31
      | ~ v1_funct_2(X31,u1_struct_0(X28),u1_struct_0(X29))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
      | ~ v1_funct_1(X30)
      | ~ sP0(X29,X28,X31) ) ),
    inference(subsumption_resolution,[],[f403,f106])).

fof(f403,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ r2_funct_2(u1_struct_0(X28),u1_struct_0(X29),X30,X31)
      | X30 = X31
      | ~ v1_funct_2(X31,u1_struct_0(X28),u1_struct_0(X29))
      | ~ v1_funct_1(X31)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
      | ~ v1_funct_1(X30)
      | ~ sP0(X29,X28,X31) ) ),
    inference(resolution,[],[f122,f109])).

fof(f2013,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_11
    | spl11_49 ),
    inference(avatar_contradiction_clause,[],[f2012])).

fof(f2012,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_11
    | spl11_49 ),
    inference(subsumption_resolution,[],[f2009,f368])).

fof(f368,plain,
    ( l1_struct_0(sK7)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl11_10
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f2009,plain,
    ( ~ l1_struct_0(sK7)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_11
    | spl11_49 ),
    inference(resolution,[],[f1979,f1554])).

fof(f1979,plain,
    ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
    | spl11_49 ),
    inference(avatar_component_clause,[],[f1977])).

fof(f1977,plain,
    ( spl11_49
  <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f2008,plain,(
    spl11_35 ),
    inference(avatar_contradiction_clause,[],[f2007])).

fof(f2007,plain,
    ( $false
    | spl11_35 ),
    inference(subsumption_resolution,[],[f2006,f270])).

fof(f2006,plain,
    ( ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(subsumption_resolution,[],[f2005,f69])).

fof(f2005,plain,
    ( v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(subsumption_resolution,[],[f2004,f70])).

fof(f2004,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(subsumption_resolution,[],[f2003,f71])).

fof(f2003,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(subsumption_resolution,[],[f2002,f75])).

fof(f2002,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(subsumption_resolution,[],[f2001,f77])).

fof(f2001,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(subsumption_resolution,[],[f1994,f80])).

fof(f1994,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_35 ),
    inference(resolution,[],[f1757,f772])).

fof(f772,plain,(
    ! [X26,X27,X25] :
      ( sP4(sK6,sK8,X25,X26,sK10,X27)
      | ~ m1_pre_topc(sK8,X26)
      | ~ m1_pre_topc(X25,X26)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ sP0(sK6,X25,X27) ) ),
    inference(subsumption_resolution,[],[f771,f107])).

fof(f771,plain,(
    ! [X26,X27,X25] :
      ( sP4(sK6,sK8,X25,X26,sK10,X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(sK6))
      | ~ m1_pre_topc(sK8,X26)
      | ~ m1_pre_topc(X25,X26)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ sP0(sK6,X25,X27) ) ),
    inference(subsumption_resolution,[],[f750,f106])).

fof(f750,plain,(
    ! [X26,X27,X25] :
      ( sP4(sK6,sK8,X25,X26,sK10,X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(sK6))
      | ~ v1_funct_1(X27)
      | ~ m1_pre_topc(sK8,X26)
      | ~ m1_pre_topc(X25,X26)
      | v2_struct_0(X25)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ sP0(sK6,X25,X27) ) ),
    inference(resolution,[],[f704,f109])).

fof(f704,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(subsumption_resolution,[],[f703,f72])).

fof(f703,plain,(
    ! [X47,X48,X49] :
      ( sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(subsumption_resolution,[],[f702,f73])).

fof(f702,plain,(
    ! [X47,X48,X49] :
      ( sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(subsumption_resolution,[],[f701,f74])).

fof(f701,plain,(
    ! [X47,X48,X49] :
      ( sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(subsumption_resolution,[],[f700,f78])).

fof(f700,plain,(
    ! [X47,X48,X49] :
      ( sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(subsumption_resolution,[],[f699,f85])).

fof(f699,plain,(
    ! [X47,X48,X49] :
      ( sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(subsumption_resolution,[],[f677,f86])).

fof(f677,plain,(
    ! [X47,X48,X49] :
      ( sP4(sK6,sK8,X47,X48,sK10,X49)
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK6))))
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(sK6))
      | ~ v1_funct_1(X49)
      | ~ m1_pre_topc(sK8,X48)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(X47,X48)
      | v2_struct_0(X47)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(X48)
      | ~ v2_pre_topc(X48)
      | v2_struct_0(X48) ) ),
    inference(resolution,[],[f130,f88])).

fof(f130,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(definition_folding,[],[f38,f46])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f1757,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_35 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f1991,plain,
    ( ~ spl11_35
    | ~ spl11_49
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f1990,f1648,f1977,f1755])).

fof(f1990,plain,
    ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f1989,f89])).

fof(f1989,plain,
    ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f1988,f77])).

fof(f1988,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f1987,f89])).

fof(f1987,plain,
    ( ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f1986,f71])).

fof(f1986,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f1985,f89])).

fof(f1985,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f1984,f70])).

fof(f1984,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f1983,f89])).

fof(f1983,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f1982,f69])).

fof(f1982,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f1981,f89])).

fof(f1981,plain,
    ( v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ v2_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f1964,f128])).

fof(f1964,plain,
    ( v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ v2_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_28 ),
    inference(resolution,[],[f1649,f129])).

fof(f1649,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK6))))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(X4),u1_struct_0(sK6))
        | ~ m1_pre_topc(sK7,X4)
        | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),X4) )
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f1648])).

fof(f1713,plain,
    ( spl11_19
    | ~ spl11_26 ),
    inference(avatar_contradiction_clause,[],[f1712])).

fof(f1712,plain,
    ( $false
    | spl11_19
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f1669,f270])).

fof(f1669,plain,
    ( ~ sP0(sK6,sK7,sK9)
    | spl11_19
    | ~ spl11_26 ),
    inference(backward_demodulation,[],[f1447,f1639])).

fof(f1639,plain,
    ( sK9 = k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f1637])).

fof(f1447,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | spl11_19 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1445,plain,
    ( spl11_19
  <=> sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f1602,plain,
    ( spl11_3
    | ~ spl11_23 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | spl11_3
    | ~ spl11_23 ),
    inference(subsumption_resolution,[],[f1599,f144])).

fof(f144,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_3
  <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1599,plain,
    ( v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ spl11_23 ),
    inference(resolution,[],[f1546,f108])).

fof(f1546,plain,
    ( sP0(sK6,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1511,plain,(
    spl11_4 ),
    inference(avatar_contradiction_clause,[],[f1510])).

fof(f1510,plain,
    ( $false
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1509,f270])).

fof(f1509,plain,
    ( ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1508,f69])).

fof(f1508,plain,
    ( v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1507,f70])).

fof(f1507,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1506,f71])).

fof(f1506,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1505,f75])).

fof(f1505,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1504,f77])).

fof(f1504,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1497,f80])).

fof(f1497,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK6,sK7,sK9)
    | spl11_4 ),
    inference(resolution,[],[f1494,f772])).

fof(f1494,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_4 ),
    inference(resolution,[],[f148,f314])).

fof(f148,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1463,plain,
    ( ~ spl11_4
    | spl11_20
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f1458,f230,f138,f134,f1460,f146])).

fof(f1458,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1457,f69])).

fof(f1457,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1456,f70])).

fof(f1456,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1455,f71])).

fof(f1455,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1454,f72])).

fof(f1454,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1453,f73])).

fof(f1453,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1452,f74])).

fof(f1452,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1451,f232])).

fof(f1451,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1450,f139])).

fof(f1450,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1449,f77])).

fof(f1449,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1431,f135])).

fof(f1431,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(duplicate_literal_removal,[],[f1402])).

fof(f1402,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)),sK9)
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(superposition,[],[f154,f532])).

fof(f532,plain,(
    ! [X59,X57,X60,X58,X56] :
      ( k3_tmap_1(X60,X57,X56,X59,X58) = k7_relat_1(X58,u1_struct_0(X59))
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
      | ~ v1_funct_1(X58)
      | ~ m1_pre_topc(X59,X56)
      | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
      | ~ m1_pre_topc(X59,X60)
      | ~ m1_pre_topc(X56,X60)
      | ~ l1_pre_topc(X57)
      | ~ v2_pre_topc(X57)
      | v2_struct_0(X57)
      | ~ l1_pre_topc(X60)
      | ~ v2_pre_topc(X60)
      | v2_struct_0(X60) ) ),
    inference(duplicate_literal_removal,[],[f529])).

fof(f529,plain,(
    ! [X59,X57,X60,X58,X56] :
      ( k3_tmap_1(X60,X57,X56,X59,X58) = k7_relat_1(X58,u1_struct_0(X59))
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
      | ~ v1_funct_1(X58)
      | ~ m1_pre_topc(X59,X56)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X57))))
      | ~ v1_funct_2(X58,u1_struct_0(X56),u1_struct_0(X57))
      | ~ v1_funct_1(X58)
      | ~ m1_pre_topc(X59,X60)
      | ~ m1_pre_topc(X56,X60)
      | ~ l1_pre_topc(X57)
      | ~ v2_pre_topc(X57)
      | v2_struct_0(X57)
      | ~ l1_pre_topc(X60)
      | ~ v2_pre_topc(X60)
      | v2_struct_0(X60) ) ),
    inference(superposition,[],[f124,f95])).

fof(f1448,plain,
    ( ~ spl11_4
    | ~ spl11_19
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(avatar_split_clause,[],[f1443,f507,f230,f138,f134,f1445,f146])).

fof(f1443,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1442,f69])).

fof(f1442,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1441,f70])).

fof(f1441,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1440,f71])).

fof(f1440,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1439,f72])).

fof(f1439,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1438,f73])).

fof(f1438,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1437,f74])).

fof(f1437,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1436,f232])).

fof(f1436,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | ~ spl11_2
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1435,f139])).

fof(f1435,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1434,f77])).

fof(f1434,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl11_1
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1432,f135])).

fof(f1432,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_15 ),
    inference(duplicate_literal_removal,[],[f1401])).

fof(f1401,plain,
    ( ~ sP0(sK6,sK7,k7_relat_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK7)))
    | ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_15 ),
    inference(superposition,[],[f509,f532])).

fof(f509,plain,
    ( ~ sP0(sK6,sK7,k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | spl11_15 ),
    inference(avatar_component_clause,[],[f507])).

fof(f789,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | spl11_2 ),
    inference(subsumption_resolution,[],[f787,f69])).

fof(f787,plain,
    ( v2_struct_0(sK5)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f786,f70])).

fof(f786,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f785,f71])).

fof(f785,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f784,f77])).

fof(f784,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f783,f80])).

fof(f783,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_2 ),
    inference(resolution,[],[f781,f756])).

fof(f756,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f755,f75])).

fof(f755,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f754,f81])).

fof(f754,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ v1_funct_1(sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f743,f82])).

fof(f743,plain,(
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
    inference(resolution,[],[f704,f84])).

fof(f781,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_2 ),
    inference(resolution,[],[f140,f247])).

fof(f140,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f780,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f779])).

fof(f779,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f778,f69])).

fof(f778,plain,
    ( v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f777,f70])).

fof(f777,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f776,f71])).

fof(f776,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f775,f77])).

fof(f775,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f774,f80])).

fof(f774,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(resolution,[],[f756,f184])).

fof(f184,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_1 ),
    inference(resolution,[],[f127,f136])).

fof(f136,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f427,plain,(
    spl11_8 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl11_8 ),
    inference(subsumption_resolution,[],[f425,f71])).

fof(f425,plain,
    ( ~ l1_pre_topc(sK5)
    | spl11_8 ),
    inference(resolution,[],[f349,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f349,plain,
    ( ~ l1_struct_0(sK5)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f347])).

fof(f397,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | spl11_13 ),
    inference(subsumption_resolution,[],[f395,f153])).

fof(f153,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f151,f71])).

fof(f151,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f94,f80])).

fof(f395,plain,
    ( ~ l1_pre_topc(sK8)
    | spl11_13 ),
    inference(resolution,[],[f383,f93])).

fof(f383,plain,
    ( ~ l1_struct_0(sK8)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f381])).

fof(f394,plain,(
    spl11_10 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl11_10 ),
    inference(subsumption_resolution,[],[f392,f152])).

fof(f152,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f150,f71])).

fof(f150,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f94,f77])).

fof(f392,plain,
    ( ~ l1_pre_topc(sK7)
    | spl11_10 ),
    inference(resolution,[],[f369,f93])).

fof(f369,plain,
    ( ~ l1_struct_0(sK7)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f367])).

fof(f391,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl11_11 ),
    inference(subsumption_resolution,[],[f389,f74])).

fof(f389,plain,
    ( ~ l1_pre_topc(sK6)
    | spl11_11 ),
    inference(resolution,[],[f373,f93])).

fof(f373,plain,
    ( ~ l1_struct_0(sK6)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f371])).

fof(f233,plain,
    ( ~ spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f175,f230,f165])).

fof(f165,plain,
    ( spl11_5
  <=> sP2(sK5,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f175,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ sP2(sK5,sK8,sK7) ),
    inference(superposition,[],[f116,f89])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f228,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl11_5 ),
    inference(subsumption_resolution,[],[f226,f69])).

fof(f226,plain,
    ( v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f225,f71])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f224,f75])).

fof(f224,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f223,f77])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f222,f78])).

fof(f222,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f221,f80])).

fof(f221,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(resolution,[],[f117,f167])).

fof(f167,plain,
    ( ~ sP2(sK5,sK8,sK7)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f42])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f149,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f92,f146,f142,f138,f134])).

fof(f92,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:41 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  543 (4408 expanded)
%              Number of leaves         :   58 (1878 expanded)
%              Depth                    :   38
%              Number of atoms          : 5011 (136809 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f202,f206,f210,f214,f215,f234,f237,f248,f515,f526,f535,f544,f553,f562,f571,f580,f589,f598,f607,f616,f625,f634,f1232,f1280,f1293,f1854,f1862,f1933,f1939,f2002,f2078])).

fof(f2078,plain,
    ( spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f2077])).

fof(f2077,plain,
    ( $false
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2076,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK5,sK2,sK3)
        & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK5)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK1,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        & v1_funct_1(sK4)
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) )
      | ~ r1_tsep_1(sK1,sK2)
      | ~ r3_tsep_1(sK0,sK1,sK2) )
    & ( ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))))
                      & v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
                      & v1_funct_2(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))
                      & v1_funct_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8)) )
                    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
                    | ~ v5_pre_topc(X8,sK2,X6)
                    | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
                    | ~ v1_funct_1(X8) )
                | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
                | ~ v5_pre_topc(X7,sK1,X6)
                | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
                | ~ v1_funct_1(X7) )
            | ~ l1_pre_topc(X6)
            | ~ v2_pre_topc(X6)
            | v2_struct_0(X6) )
        & r1_tsep_1(sK1,sK2) )
      | r3_tsep_1(sK0,sK1,sK2) )
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f44,f43,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(X5,X2,X3)
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(X4,X1,X3)
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( ( ! [X6] :
                        ( ! [X7] :
                            ( ! [X8] :
                                ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))))
                                  & v5_pre_topc(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_tsep_1(X0,X1,X2),X6)
                                  & v1_funct_2(k10_tmap_1(X0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))
                                  & v1_funct_1(k10_tmap_1(X0,X6,X1,X2,X7,X8)) )
                                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                                | ~ v5_pre_topc(X8,X2,X6)
                                | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                                | ~ v1_funct_1(X8) )
                            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                            | ~ v5_pre_topc(X7,X1,X6)
                            | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                            | ~ v1_funct_1(X7) )
                        | ~ l1_pre_topc(X6)
                        | ~ v2_pre_topc(X6)
                        | v2_struct_0(X6) )
                    & r1_tsep_1(X1,X2) )
                  | r3_tsep_1(X0,X1,X2) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(sK0,X3,X1,X2,X4,X5),k1_tsep_1(sK0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(sK0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(sK0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(sK0,X1,X2) )
              & ( ( ! [X6] :
                      ( ! [X7] :
                          ( ! [X8] :
                              ( ( m1_subset_1(k10_tmap_1(sK0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X6))))
                                & v5_pre_topc(k10_tmap_1(sK0,X6,X1,X2,X7,X8),k1_tsep_1(sK0,X1,X2),X6)
                                & v1_funct_2(k10_tmap_1(sK0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X6))
                                & v1_funct_1(k10_tmap_1(sK0,X6,X1,X2,X7,X8)) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                              | ~ v5_pre_topc(X8,X2,X6)
                              | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                              | ~ v1_funct_1(X8) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X7,X1,X6)
                          | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                          | ~ v1_funct_1(X7) )
                      | ~ l1_pre_topc(X6)
                      | ~ v2_pre_topc(X6)
                      | v2_struct_0(X6) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(sK0,X1,X2) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X3,X1,X2,X4,X5),k1_tsep_1(sK0,X1,X2),X3)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X3,X1,X2,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(X5,X2,X3)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                      & v5_pre_topc(X4,X1,X3)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & l1_pre_topc(X3)
                  & v2_pre_topc(X3)
                  & ~ v2_struct_0(X3) )
              | ~ r1_tsep_1(X1,X2)
              | ~ r3_tsep_1(sK0,X1,X2) )
            & ( ( ! [X6] :
                    ( ! [X7] :
                        ( ! [X8] :
                            ( ( m1_subset_1(k10_tmap_1(sK0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X6))))
                              & v5_pre_topc(k10_tmap_1(sK0,X6,X1,X2,X7,X8),k1_tsep_1(sK0,X1,X2),X6)
                              & v1_funct_2(k10_tmap_1(sK0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(sK0,X1,X2)),u1_struct_0(X6))
                              & v1_funct_1(k10_tmap_1(sK0,X6,X1,X2,X7,X8)) )
                            | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                            | ~ v5_pre_topc(X8,X2,X6)
                            | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                            | ~ v1_funct_1(X8) )
                        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                        | ~ v5_pre_topc(X7,X1,X6)
                        | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                        | ~ v1_funct_1(X7) )
                    | ~ l1_pre_topc(X6)
                    | ~ v2_pre_topc(X6)
                    | v2_struct_0(X6) )
                & r1_tsep_1(X1,X2) )
              | r3_tsep_1(sK0,X1,X2) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,sK1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k10_tmap_1(sK0,X3,sK1,X2,X4,X5),k1_tsep_1(sK0,sK1,X2),X3)
                          | ~ v1_funct_2(k10_tmap_1(sK0,X3,sK1,X2,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(k10_tmap_1(sK0,X3,sK1,X2,X4,X5)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v5_pre_topc(X5,X2,X3)
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
                    & v5_pre_topc(X4,sK1,X3)
                    & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                & l1_pre_topc(X3)
                & v2_pre_topc(X3)
                & ~ v2_struct_0(X3) )
            | ~ r1_tsep_1(sK1,X2)
            | ~ r3_tsep_1(sK0,sK1,X2) )
          & ( ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X6))))
                            & v5_pre_topc(k10_tmap_1(sK0,X6,sK1,X2,X7,X8),k1_tsep_1(sK0,sK1,X2),X6)
                            & v1_funct_2(k10_tmap_1(sK0,X6,sK1,X2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X6))
                            & v1_funct_1(k10_tmap_1(sK0,X6,sK1,X2,X7,X8)) )
                          | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X8,X2,X6)
                          | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                          | ~ v1_funct_1(X8) )
                      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X7,sK1,X6)
                      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
                      | ~ v1_funct_1(X7) )
                  | ~ l1_pre_topc(X6)
                  | ~ v2_pre_topc(X6)
                  | v2_struct_0(X6) )
              & r1_tsep_1(sK1,X2) )
            | r3_tsep_1(sK0,sK1,X2) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,sK1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X3))))
                        | ~ v5_pre_topc(k10_tmap_1(sK0,X3,sK1,X2,X4,X5),k1_tsep_1(sK0,sK1,X2),X3)
                        | ~ v1_funct_2(k10_tmap_1(sK0,X3,sK1,X2,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X3))
                        | ~ v1_funct_1(k10_tmap_1(sK0,X3,sK1,X2,X4,X5)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v5_pre_topc(X5,X2,X3)
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
                  & v5_pre_topc(X4,sK1,X3)
                  & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X3))
                  & v1_funct_1(X4) )
              & l1_pre_topc(X3)
              & v2_pre_topc(X3)
              & ~ v2_struct_0(X3) )
          | ~ r1_tsep_1(sK1,X2)
          | ~ r3_tsep_1(sK0,sK1,X2) )
        & ( ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X6))))
                          & v5_pre_topc(k10_tmap_1(sK0,X6,sK1,X2,X7,X8),k1_tsep_1(sK0,sK1,X2),X6)
                          & v1_funct_2(k10_tmap_1(sK0,X6,sK1,X2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,X2)),u1_struct_0(X6))
                          & v1_funct_1(k10_tmap_1(sK0,X6,sK1,X2,X7,X8)) )
                        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                        | ~ v5_pre_topc(X8,X2,X6)
                        | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                        | ~ v1_funct_1(X8) )
                    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
                    | ~ v5_pre_topc(X7,sK1,X6)
                    | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
                    | ~ v1_funct_1(X7) )
                | ~ l1_pre_topc(X6)
                | ~ v2_pre_topc(X6)
                | v2_struct_0(X6) )
            & r1_tsep_1(sK1,X2) )
          | r3_tsep_1(sK0,sK1,X2) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5),k1_tsep_1(sK0,sK1,sK2),X3)
                      | ~ v1_funct_2(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                    & v5_pre_topc(X5,sK2,X3)
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
                & v5_pre_topc(X4,sK1,X3)
                & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(sK1,sK2)
        | ~ r3_tsep_1(sK0,sK1,sK2) )
      & ( ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))))
                        & v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
                        & v1_funct_2(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))
                        & v1_funct_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8)) )
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X8,sK2,X6)
                      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
                  | ~ v5_pre_topc(X7,sK1,X6)
                  | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
                  | ~ v1_funct_1(X7) )
              | ~ l1_pre_topc(X6)
              | ~ v2_pre_topc(X6)
              | v2_struct_0(X6) )
          & r1_tsep_1(sK1,sK2) )
        | r3_tsep_1(sK0,sK1,sK2) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5),k1_tsep_1(sK0,sK1,sK2),X3)
                  | ~ v1_funct_2(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X3))
                  | ~ v1_funct_1(k10_tmap_1(sK0,X3,sK1,sK2,X4,X5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                & v5_pre_topc(X5,sK2,X3)
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
            & v5_pre_topc(X4,sK1,X3)
            & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X3))
            & v1_funct_1(X4) )
        & l1_pre_topc(X3)
        & v2_pre_topc(X3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5),k1_tsep_1(sK0,sK1,sK2),sK3)
                | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
                | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v5_pre_topc(X5,sK2,sK3)
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
          & v5_pre_topc(X4,sK1,sK3)
          & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5),k1_tsep_1(sK0,sK1,sK2),sK3)
              | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
              | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,X4,X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v5_pre_topc(X5,sK2,sK3)
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        & v5_pre_topc(X4,sK1,sK3)
        & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5),k1_tsep_1(sK0,sK1,sK2),sK3)
            | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
            | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(X5,sK2,sK3)
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
      & v5_pre_topc(sK4,sK1,sK3)
      & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5),k1_tsep_1(sK0,sK1,sK2),sK3)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,X5)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(X5,sK2,sK3)
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v5_pre_topc(sK5,sK2,sK3)
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X6] :
                      ( ! [X7] :
                          ( ! [X8] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))))
                                & v5_pre_topc(k10_tmap_1(X0,X6,X1,X2,X7,X8),k1_tsep_1(X0,X1,X2),X6)
                                & v1_funct_2(k10_tmap_1(X0,X6,X1,X2,X7,X8),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X6))
                                & v1_funct_1(k10_tmap_1(X0,X6,X1,X2,X7,X8)) )
                              | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X6))))
                              | ~ v5_pre_topc(X8,X2,X6)
                              | ~ v1_funct_2(X8,u1_struct_0(X2),u1_struct_0(X6))
                              | ~ v1_funct_1(X8) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                          | ~ v5_pre_topc(X7,X1,X6)
                          | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                          | ~ v1_funct_1(X7) )
                      | ~ l1_pre_topc(X6)
                      | ~ v2_pre_topc(X6)
                      | v2_struct_0(X6) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v5_pre_topc(X5,X2,X3)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                        & v5_pre_topc(X4,X1,X3)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(X4,X1,X3)
                              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(X5,X2,X3)
                                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(X5) )
                               => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                  & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                  & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                  & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X1,X3)
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(X5,X2,X3)
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_tmap_1)).

fof(f2076,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2075,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f2075,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2074,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f2074,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2073,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f2073,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2072,f59])).

fof(f59,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f2072,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2071,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f2071,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2070,f61])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f2070,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2069,f1369])).

fof(f1369,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1368,f246])).

fof(f246,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f220,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f220,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f218,f57])).

fof(f218,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f80,f61])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1368,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f293,f235])).

fof(f235,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f219,f79])).

fof(f219,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f217,f57])).

fof(f217,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f80,f59])).

fof(f293,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl8_24 ),
    inference(resolution,[],[f233,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f233,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl8_24
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f2069,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f2068,f122])).

fof(f122,plain,
    ( ~ r3_tsep_1(sK0,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_1
  <=> r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2068,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_30 ),
    inference(resolution,[],[f475,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ( ( ~ m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
                      | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
                      | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
                      | ~ v1_funct_1(sK7(X0,X1,X2)) )
                    & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
                    & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),X2,sK6(X0,X1,X2))
                    & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)))
                    & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
                    & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),X1,sK6(X0,X1,X2))
                    & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)))
                    & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
                    & v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
                    & v1_funct_1(sK7(X0,X1,X2))
                    & l1_pre_topc(sK6(X0,X1,X2))
                    & v2_pre_topc(sK6(X0,X1,X2))
                    & ~ v2_struct_0(sK6(X0,X1,X2)) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                              & v5_pre_topc(X6,k1_tsep_1(X0,X1,X2),X5)
                              & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                              & v1_funct_1(X6) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),X2,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6))
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),X1,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                            | ~ v1_funct_1(X6) )
                        | ~ l1_pre_topc(X5)
                        | ~ v2_pre_topc(X5)
                        | v2_struct_0(X5) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),X2,sK6(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4))
            & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),X1,sK6(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK6(X0,X1,X2))
        & v2_pre_topc(sK6(X0,X1,X2))
        & ~ v2_struct_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),X2,sK6(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,X4))
          & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),X1,sK6(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
          | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
          | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
          | ~ v1_funct_1(sK7(X0,X1,X2)) )
        & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
        & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),X2,sK6(X0,X1,X2))
        & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
        & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)))
        & m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
        & v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),X1,sK6(X0,X1,X2))
        & v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
        & v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
        & v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X5] :
                        ( ! [X6] :
                            ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                              & v5_pre_topc(X6,k1_tsep_1(X0,X1,X2),X5)
                              & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                              & v1_funct_1(X6) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),X2,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6),u1_struct_0(X2),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X2,X6))
                            | ~ m1_subset_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),X1,X5)
                            | ~ v1_funct_2(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                            | ~ v1_funct_1(k3_tmap_1(X0,X5,k1_tsep_1(X0,X1,X2),X1,X6))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))))
                            | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X5))
                            | ~ v1_funct_1(X6) )
                        | ~ l1_pre_topc(X5)
                        | ~ v2_pre_topc(X5)
                        | v2_struct_0(X5) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            | ~ v1_funct_1(X4) )
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) )
                           => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).

fof(f475,plain,
    ( v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl8_30
  <=> v2_struct_0(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f2002,plain,
    ( spl8_1
    | ~ spl8_19
    | ~ spl8_24
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_45
    | ~ spl8_46
    | ~ spl8_47
    | ~ spl8_48
    | ~ spl8_89 ),
    inference(avatar_contradiction_clause,[],[f2001])).

fof(f2001,plain,
    ( $false
    | spl8_1
    | ~ spl8_19
    | ~ spl8_24
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_45
    | ~ spl8_46
    | ~ spl8_47
    | ~ spl8_48
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f2000,f1590])).

fof(f1590,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1589,f55])).

fof(f1589,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1588,f56])).

fof(f1588,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1587,f57])).

fof(f1587,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1586,f58])).

fof(f1586,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1585,f59])).

fof(f1585,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1584,f60])).

fof(f1584,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1583,f61])).

fof(f1583,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_24
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1582,f1369])).

fof(f1582,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1581,f615])).

fof(f615,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl8_46
  <=> v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f1581,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_42
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f1580,f606])).

fof(f606,plain,
    ( v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f604])).

fof(f604,plain,
    ( spl8_45
  <=> v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f1580,plain,
    ( ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f1574,f122])).

fof(f1574,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_42 ),
    inference(resolution,[],[f579,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ v5_pre_topc(sK7(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK6(X0,X1,X2))
      | ~ v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
      | ~ v1_funct_1(sK7(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f579,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f577])).

fof(f577,plain,
    ( spl8_42
  <=> m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f2000,plain,
    ( v5_pre_topc(sK7(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl8_19
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | ~ spl8_89 ),
    inference(superposition,[],[f1927,f1853])).

fof(f1853,plain,
    ( sK7(sK0,sK1,sK2) = k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f1851,plain,
    ( spl8_89
  <=> sK7(sK0,sK1,sK2) = k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f1927,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl8_19
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1926,f561])).

fof(f561,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl8_40
  <=> v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f1926,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl8_19
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1925,f543])).

fof(f543,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl8_38
  <=> v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1925,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl8_19
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1924,f588])).

fof(f588,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl8_43
  <=> v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f1924,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl8_19
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(resolution,[],[f1643,f525])).

fof(f525,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl8_36
  <=> m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f1643,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2)) )
    | ~ spl8_19
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1642,f570])).

fof(f570,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl8_41
  <=> v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f1642,plain,
    ( ! [X2] :
        ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_19
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1641,f552])).

fof(f552,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl8_39
  <=> v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f1641,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_19
    | spl8_30
    | ~ spl8_37
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1640,f597])).

fof(f597,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl8_44
  <=> v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f1640,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_19
    | spl8_30
    | ~ spl8_37
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1639,f624])).

fof(f624,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f622])).

fof(f622,plain,
    ( spl8_47
  <=> l1_pre_topc(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f1639,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_19
    | spl8_30
    | ~ spl8_37
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1638,f633])).

fof(f633,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f631])).

fof(f631,plain,
    ( spl8_48
  <=> v2_pre_topc(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f1638,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_19
    | spl8_30
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1620,f474])).

fof(f474,plain,
    ( ~ v2_struct_0(sK6(sK0,sK1,sK2))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f473])).

fof(f1620,plain,
    ( ! [X2] :
        ( v2_struct_0(sK6(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v5_pre_topc(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X2),k1_tsep_1(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X2,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_19
    | ~ spl8_37 ),
    inference(resolution,[],[f534,f205])).

fof(f205,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_19
  <=> ! [X7,X8,X6] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f534,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl8_37
  <=> m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f1939,plain,
    ( ~ spl8_18
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | spl8_88 ),
    inference(avatar_contradiction_clause,[],[f1938])).

fof(f1938,plain,
    ( $false
    | ~ spl8_18
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | spl8_88 ),
    inference(subsumption_resolution,[],[f1937,f1849])).

fof(f1849,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | spl8_88 ),
    inference(avatar_component_clause,[],[f1847])).

fof(f1847,plain,
    ( spl8_88
  <=> m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f1937,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_18
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1936,f561])).

fof(f1936,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_18
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1935,f543])).

fof(f1935,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_18
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1934,f588])).

fof(f1934,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_18
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(resolution,[],[f1631,f525])).

fof(f1631,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1630,f570])).

fof(f1630,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1629,f552])).

fof(f1629,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | spl8_30
    | ~ spl8_37
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1628,f597])).

fof(f1628,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | spl8_30
    | ~ spl8_37
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1627,f624])).

fof(f1627,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | spl8_30
    | ~ spl8_37
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1626,f633])).

fof(f1626,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | spl8_30
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1618,f474])).

fof(f1618,plain,
    ( ! [X0] :
        ( v2_struct_0(sK6(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X0,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_18
    | ~ spl8_37 ),
    inference(resolution,[],[f534,f201])).

fof(f201,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | m1_subset_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_18
  <=> ! [X7,X8,X6] :
        ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1933,plain,
    ( ~ spl8_20
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | spl8_87 ),
    inference(avatar_contradiction_clause,[],[f1932])).

fof(f1932,plain,
    ( $false
    | ~ spl8_20
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | spl8_87 ),
    inference(subsumption_resolution,[],[f1931,f1845])).

fof(f1845,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | spl8_87 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f1843,plain,
    ( spl8_87
  <=> v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f1931,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_20
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1930,f561])).

fof(f1930,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_20
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1929,f543])).

fof(f1929,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_20
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1928,f588])).

fof(f1928,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_20
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(resolution,[],[f1637,f525])).

fof(f1637,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2))) )
    | ~ spl8_20
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1636,f570])).

fof(f1636,plain,
    ( ! [X1] :
        ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_20
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1635,f552])).

fof(f1635,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_20
    | spl8_30
    | ~ spl8_37
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1634,f597])).

fof(f1634,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_20
    | spl8_30
    | ~ spl8_37
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1633,f624])).

fof(f1633,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_20
    | spl8_30
    | ~ spl8_37
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1632,f633])).

fof(f1632,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_20
    | spl8_30
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1619,f474])).

fof(f1619,plain,
    ( ! [X1] :
        ( v2_struct_0(sK6(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X1),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X1,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_20
    | ~ spl8_37 ),
    inference(resolution,[],[f534,f209])).

fof(f209,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | v1_funct_2(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_20
  <=> ! [X7,X8,X6] :
        ( v1_funct_2(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1862,plain,
    ( ~ spl8_21
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | spl8_86 ),
    inference(avatar_contradiction_clause,[],[f1861])).

fof(f1861,plain,
    ( $false
    | ~ spl8_21
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48
    | spl8_86 ),
    inference(subsumption_resolution,[],[f1860,f1841])).

fof(f1841,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | spl8_86 ),
    inference(avatar_component_clause,[],[f1839])).

fof(f1839,plain,
    ( spl8_86
  <=> v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f1860,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ spl8_21
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1859,f561])).

fof(f1859,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ spl8_21
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1858,f543])).

fof(f1858,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ spl8_21
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_43
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1857,f588])).

fof(f1857,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ spl8_21
    | spl8_30
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(resolution,[],[f1649,f525])).

fof(f1649,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3)) )
    | ~ spl8_21
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_41
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1648,f570])).

fof(f1648,plain,
    ( ! [X3] :
        ( ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_21
    | spl8_30
    | ~ spl8_37
    | ~ spl8_39
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1647,f552])).

fof(f1647,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_21
    | spl8_30
    | ~ spl8_37
    | ~ spl8_44
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1646,f597])).

fof(f1646,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_21
    | spl8_30
    | ~ spl8_37
    | ~ spl8_47
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1645,f624])).

fof(f1645,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_21
    | spl8_30
    | ~ spl8_37
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f1644,f633])).

fof(f1644,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_21
    | spl8_30
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1621,f474])).

fof(f1621,plain,
    ( ! [X3] :
        ( v2_struct_0(sK6(sK0,sK1,sK2))
        | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
        | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
        | v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),X3))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
        | ~ v5_pre_topc(X3,sK2,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2))))) )
    | ~ spl8_21
    | ~ spl8_37 ),
    inference(resolution,[],[f534,f213])).

fof(f213,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | v1_funct_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl8_21
  <=> ! [X7,X8,X6] :
        ( v1_funct_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f1854,plain,
    ( ~ spl8_86
    | ~ spl8_87
    | ~ spl8_88
    | spl8_89
    | ~ spl8_35
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f1837,f613,f604,f577,f512,f1851,f1847,f1843,f1839])).

fof(f512,plain,
    ( spl8_35
  <=> r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1837,plain,
    ( sK7(sK0,sK1,sK2) = k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ spl8_35
    | ~ spl8_42
    | ~ spl8_45
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f1836,f615])).

fof(f1836,plain,
    ( sK7(sK0,sK1,sK2) = k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_35
    | ~ spl8_42
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f1835,f606])).

fof(f1835,plain,
    ( sK7(sK0,sK1,sK2) = k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_35
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f1834,f579])).

fof(f1834,plain,
    ( sK7(sK0,sK1,sK2) = k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_35 ),
    inference(resolution,[],[f514,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f514,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f512])).

fof(f1293,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1292])).

fof(f1292,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1291,f55])).

fof(f1291,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1290,f56])).

fof(f1290,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1289,f57])).

fof(f1289,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1288,f58])).

fof(f1288,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1287,f59])).

fof(f1287,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1286,f60])).

fof(f1286,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1285,f61])).

fof(f1285,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f637,f126])).

fof(f126,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f637,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f121,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1280,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f1279])).

fof(f1279,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1278,f246])).

fof(f1278,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1277,f235])).

fof(f1277,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f293,f1267])).

fof(f1267,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(global_subsumption,[],[f78,f121,f1239,f1247,f1255,f137])).

fof(f137,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_5
  <=> v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1255,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1254,f55])).

fof(f1254,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1253,f56])).

fof(f1253,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1252,f57])).

fof(f1252,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f926,f59])).

fof(f926,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f811,f61])).

fof(f811,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | v1_funct_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f810,f58])).

fof(f810,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5))
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f809,f182])).

fof(f182,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_14
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f809,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f804,f177])).

fof(f177,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_13
  <=> v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f804,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5))
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f688,f167])).

fof(f167,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f688,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f687,f197])).

fof(f197,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl8_17
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f687,plain,
    ( ! [X6,X8,X7] :
        ( v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f686,f192])).

fof(f192,plain,
    ( v2_pre_topc(sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_16
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f686,plain,
    ( ! [X6,X8,X7] :
        ( v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f685,f187])).

fof(f187,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_15
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f685,plain,
    ( ! [X6,X8,X7] :
        ( v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f684,f60])).

fof(f684,plain,
    ( ! [X6,X8,X7] :
        ( v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f683,f162])).

fof(f162,plain,
    ( v1_funct_1(sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_10
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f683,plain,
    ( ! [X6,X8,X7] :
        ( v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f669,f157])).

fof(f157,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_9
  <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f669,plain,
    ( ! [X6,X8,X7] :
        ( v1_funct_1(k10_tmap_1(X6,sK3,X7,sK2,X8,sK5))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK3))))
        | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(sK3))
        | ~ v1_funct_1(X8)
        | ~ m1_pre_topc(sK2,X6)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_7 ),
    inference(resolution,[],[f147,f114])).

fof(f114,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f147,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_7
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1247,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1246,f55])).

fof(f1246,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1245,f56])).

fof(f1245,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1244,f57])).

fof(f1244,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f951,f59])).

fof(f951,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f829,f61])).

fof(f829,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | v1_funct_2(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f828,f58])).

fof(f828,plain,
    ( ! [X1] :
        ( v1_funct_2(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f827,f182])).

fof(f827,plain,
    ( ! [X1] :
        ( v1_funct_2(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f822,f177])).

fof(f822,plain,
    ( ! [X1] :
        ( v1_funct_2(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f682,f167])).

fof(f682,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f681,f197])).

fof(f681,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f680,f192])).

fof(f680,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f679,f187])).

fof(f679,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f678,f60])).

fof(f678,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f677,f162])).

fof(f677,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f668,f157])).

fof(f668,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k10_tmap_1(X3,sK3,X4,sK2,X5,sK5),u1_struct_0(k1_tsep_1(X3,X4,sK2)),u1_struct_0(sK3))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(sK2,X3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_7 ),
    inference(resolution,[],[f147,f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f35])).

fof(f1239,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1238,f55])).

fof(f1238,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1237,f56])).

fof(f1237,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1236,f57])).

fof(f1236,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f958,f59])).

fof(f958,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f847,f61])).

fof(f847,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | m1_subset_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f846,f58])).

fof(f846,plain,
    ( ! [X1] :
        ( m1_subset_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))))
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f845,f182])).

fof(f845,plain,
    ( ! [X1] :
        ( m1_subset_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f840,f177])).

fof(f840,plain,
    ( ! [X1] :
        ( m1_subset_1(k10_tmap_1(X1,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK1,sK2)),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f676,f167])).

fof(f676,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f675,f197])).

fof(f675,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f674,f192])).

fof(f674,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f673,f187])).

fof(f673,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f672,f60])).

fof(f672,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f671,f162])).

fof(f671,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f667,f157])).

fof(f667,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(X0,sK3,X1,sK2,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f147,f116])).

fof(f116,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1232,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f1231])).

fof(f1231,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1230,f182])).

fof(f1230,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1229,f177])).

fof(f1229,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1228,f172])).

fof(f172,plain,
    ( v5_pre_topc(sK4,sK1,sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_12
  <=> v5_pre_topc(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1228,plain,
    ( ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f1227,f138])).

fof(f138,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1227,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,sK4,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(resolution,[],[f981,f167])).

fof(f981,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(subsumption_resolution,[],[f980,f197])).

fof(f980,plain,
    ( ! [X0] :
        ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0)
        | v2_struct_0(sK3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f979,f192])).

fof(f979,plain,
    ( ! [X0] :
        ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f978,f187])).

fof(f978,plain,
    ( ! [X0] :
        ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f977,f162])).

fof(f977,plain,
    ( ! [X0] :
        ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f976,f157])).

fof(f976,plain,
    ( ! [X0] :
        ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f975,f152])).

fof(f152,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_8
  <=> v5_pre_topc(sK5,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f975,plain,
    ( ! [X0] :
        ( v5_pre_topc(k10_tmap_1(sK0,sK3,sK1,sK2,X0,sK5),k1_tsep_1(sK0,sK1,sK2),sK3)
        | ~ v5_pre_topc(sK5,sK2,sK3)
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X0,sK1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(resolution,[],[f802,f147])).

fof(f802,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f801,f55])).

fof(f801,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f800,f56])).

fof(f800,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f799,f57])).

fof(f799,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f798,f58])).

fof(f798,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f797,f59])).

fof(f797,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f796,f60])).

fof(f796,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f795,f61])).

fof(f795,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f664,f125])).

fof(f125,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f664,plain,
    ( ! [X6,X8,X7] :
        ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(X8,sK2,X6)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
        | ~ v5_pre_topc(X7,sK1,X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ r1_tsep_1(sK1,sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f645,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
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
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
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

fof(f10,axiom,(
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
                 => ( r1_tsep_1(X2,X3)
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
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

fof(f645,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f644,f55])).

fof(f644,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f643,f56])).

fof(f643,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f642,f57])).

fof(f642,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f641,f58])).

fof(f641,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f640,f59])).

fof(f640,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f639,f60])).

fof(f639,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f636,f61])).

fof(f636,plain,
    ( r4_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f121,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tsep_1)).

fof(f634,plain,
    ( spl8_48
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f629,f124,f120,f631])).

fof(f629,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f628,f55])).

fof(f628,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f627,f56])).

fof(f627,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f626,f57])).

fof(f626,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f372,f59])).

fof(f372,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f251,f61])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v2_pre_topc(sK6(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f250,f58])).

fof(f250,plain,
    ( ! [X0] :
        ( v2_pre_topc(sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f249,f60])).

fof(f249,plain,
    ( ! [X0] :
        ( v2_pre_topc(sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f92,f125])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v2_pre_topc(sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f625,plain,
    ( spl8_47
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f620,f124,f120,f622])).

fof(f620,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f619,f55])).

fof(f619,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | l1_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f618,f56])).

fof(f618,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f617,f57])).

fof(f617,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f378,f59])).

fof(f378,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f254,f61])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | l1_pre_topc(sK6(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f253,f58])).

fof(f253,plain,
    ( ! [X0] :
        ( l1_pre_topc(sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f252,f60])).

fof(f252,plain,
    ( ! [X0] :
        ( l1_pre_topc(sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f93,f125])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | l1_pre_topc(sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f616,plain,
    ( spl8_46
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f611,f124,f120,f613])).

fof(f611,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f610,f55])).

fof(f610,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f609,f56])).

fof(f609,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f608,f57])).

fof(f608,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f384,f59])).

fof(f384,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f257,f61])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v1_funct_1(sK7(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f256,f58])).

fof(f256,plain,
    ( ! [X0] :
        ( v1_funct_1(sK7(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f255,f60])).

fof(f255,plain,
    ( ! [X0] :
        ( v1_funct_1(sK7(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f94,f125])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v1_funct_1(sK7(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f607,plain,
    ( spl8_45
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f602,f124,f120,f604])).

fof(f602,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f601,f55])).

fof(f601,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f600,f56])).

fof(f600,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f599,f57])).

fof(f599,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f390,f59])).

fof(f390,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f260,f61])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v1_funct_2(sK7(X0,sK1,sK2),u1_struct_0(k1_tsep_1(X0,sK1,sK2)),u1_struct_0(sK6(X0,sK1,sK2)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f259,f58])).

fof(f259,plain,
    ( ! [X0] :
        ( v1_funct_2(sK7(X0,sK1,sK2),u1_struct_0(k1_tsep_1(X0,sK1,sK2)),u1_struct_0(sK6(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f258,f60])).

fof(f258,plain,
    ( ! [X0] :
        ( v1_funct_2(sK7(X0,sK1,sK2),u1_struct_0(k1_tsep_1(X0,sK1,sK2)),u1_struct_0(sK6(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f95,f125])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v1_funct_2(sK7(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f598,plain,
    ( spl8_44
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f593,f124,f120,f595])).

fof(f593,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f592,f55])).

fof(f592,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f591,f56])).

fof(f591,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f590,f57])).

fof(f590,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f396,f59])).

fof(f396,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f263,f61])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v1_funct_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f262,f58])).

fof(f262,plain,
    ( ! [X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f261,f60])).

fof(f261,plain,
    ( ! [X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f97,f125])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f589,plain,
    ( spl8_43
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f584,f124,f120,f586])).

fof(f584,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f583,f55])).

fof(f583,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f582,f56])).

fof(f582,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f581,f57])).

fof(f581,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f402,f59])).

fof(f402,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f266,f61])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v1_funct_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f265,f58])).

fof(f265,plain,
    ( ! [X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f264,f60])).

fof(f264,plain,
    ( ! [X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f101,f125])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v1_funct_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f580,plain,
    ( spl8_42
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f575,f124,f120,f577])).

fof(f575,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f574,f55])).

fof(f574,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f573,f56])).

fof(f573,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f572,f57])).

fof(f572,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f408,f59])).

fof(f408,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f269,f61])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | m1_subset_1(sK7(X0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK1,sK2)),u1_struct_0(sK6(X0,sK1,sK2)))))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f268,f58])).

fof(f268,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(X0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK1,sK2)),u1_struct_0(sK6(X0,sK1,sK2)))))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f267,f60])).

fof(f267,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(X0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK1,sK2)),u1_struct_0(sK6(X0,sK1,sK2)))))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f96,f125])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f571,plain,
    ( spl8_41
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f566,f124,f120,f568])).

fof(f566,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f565,f55])).

fof(f565,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f564,f56])).

fof(f564,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f563,f57])).

fof(f563,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f414,f59])).

fof(f414,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),sK1,sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f272,f61])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v5_pre_topc(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),sK1,sK6(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f271,f58])).

fof(f271,plain,
    ( ! [X0] :
        ( v5_pre_topc(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),sK1,sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f270,f60])).

fof(f270,plain,
    ( ! [X0] :
        ( v5_pre_topc(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),sK1,sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f99,f125])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),X1,sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f562,plain,
    ( spl8_40
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f557,f124,f120,f559])).

fof(f557,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f556,f55])).

fof(f556,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f555,f56])).

fof(f555,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f554,f57])).

fof(f554,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f420,f59])).

fof(f420,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v5_pre_topc(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),sK2,sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f275,f61])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v5_pre_topc(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),sK2,sK6(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f274,f58])).

fof(f274,plain,
    ( ! [X0] :
        ( v5_pre_topc(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),sK2,sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f273,f60])).

fof(f273,plain,
    ( ! [X0] :
        ( v5_pre_topc(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),sK2,sK6(X0,sK1,sK2))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f103,f125])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v5_pre_topc(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),X2,sK6(X0,X1,X2))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f553,plain,
    ( spl8_39
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f548,f124,f120,f550])).

fof(f548,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f547,f55])).

fof(f547,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f546,f56])).

fof(f546,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f545,f57])).

fof(f545,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f426,f59])).

fof(f426,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f278,f61])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v1_funct_2(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(X0,sK1,sK2)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f277,f58])).

fof(f277,plain,
    ( ! [X0] :
        ( v1_funct_2(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f276,f60])).

fof(f276,plain,
    ( ! [X0] :
        ( v1_funct_2(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK6(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f98,f125])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f544,plain,
    ( spl8_38
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f539,f124,f120,f541])).

fof(f539,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f538,f55])).

fof(f538,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f537,f56])).

fof(f537,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f536,f57])).

fof(f536,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f432,f59])).

fof(f432,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f281,f61])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | v1_funct_2(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(X0,sK1,sK2)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f280,f58])).

fof(f280,plain,
    ( ! [X0] :
        ( v1_funct_2(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f279,f60])).

fof(f279,plain,
    ( ! [X0] :
        ( v1_funct_2(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK6(X0,sK1,sK2)))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f102,f125])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | v1_funct_2(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f535,plain,
    ( spl8_37
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f530,f124,f120,f532])).

fof(f530,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f529,f55])).

fof(f529,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f528,f56])).

fof(f528,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f527,f57])).

fof(f527,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f438,f59])).

fof(f438,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f319,f61])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | m1_subset_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(X0,sK1,sK2)))))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f318,f58])).

fof(f318,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(X0,sK1,sK2)))))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f316,f60])).

fof(f316,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK1,sK7(X0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK6(X0,sK1,sK2)))))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f100,f125])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f526,plain,
    ( spl8_36
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f521,f124,f120,f523])).

fof(f521,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f520,f55])).

fof(f520,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f519,f56])).

fof(f519,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f518,f57])).

fof(f518,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f445,f59])).

fof(f445,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | m1_subset_1(k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f325,f61])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | r3_tsep_1(X0,sK1,sK2)
        | m1_subset_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(X0,sK1,sK2)))))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f324,f58])).

fof(f324,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(X0,sK1,sK2)))))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f322,f60])).

fof(f322,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_tmap_1(X0,sK6(X0,sK1,sK2),k1_tsep_1(X0,sK1,sK2),sK2,sK7(X0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK6(X0,sK1,sK2)))))
        | r3_tsep_1(X0,sK1,sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f104,f125])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | m1_subset_1(k3_tmap_1(X0,sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK7(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6(X0,X1,X2)))))
      | r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f515,plain,
    ( spl8_30
    | spl8_35
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f510,f124,f120,f512,f473])).

fof(f510,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f509,f55])).

fof(f509,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f508,f56])).

fof(f508,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f507,f57])).

fof(f507,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f506,f377])).

fof(f377,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f376,f55])).

fof(f376,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f375,f56])).

fof(f375,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f374,f57])).

fof(f374,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f373,f59])).

fof(f373,plain,
    ( v2_pre_topc(sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f372,f122])).

fof(f506,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f505,f383])).

fof(f383,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f382,f55])).

fof(f382,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f381,f56])).

fof(f381,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f380,f57])).

fof(f380,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f379,f59])).

fof(f379,plain,
    ( l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f378,f122])).

fof(f505,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f504,f58])).

fof(f504,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f503,f59])).

fof(f503,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f502,f60])).

fof(f502,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f501,f61])).

fof(f501,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f500,f389])).

fof(f389,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f388,f55])).

fof(f388,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f387,f56])).

fof(f387,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f386,f57])).

fof(f386,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f385,f59])).

fof(f385,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f384,f122])).

fof(f500,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f455,f395])).

fof(f395,plain,
    ( v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f394,f55])).

fof(f394,plain,
    ( v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f393,f56])).

fof(f393,plain,
    ( v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f392,f57])).

fof(f392,plain,
    ( v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f391,f59])).

fof(f391,plain,
    ( v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f390,f122])).

fof(f455,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)),sK7(sK0,sK1,sK2),k10_tmap_1(sK0,sK6(sK0,sK1,sK2),sK1,sK2,k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK1,sK7(sK0,sK1,sK2)),k3_tmap_1(sK0,sK6(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2),sK2,sK7(sK0,sK1,sK2))))
    | ~ v1_funct_2(sK7(sK0,sK1,sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK6(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK6(sK0,sK1,sK2))
    | v2_struct_0(sK6(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f413,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f413,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f412,f55])).

fof(f412,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f411,f56])).

fof(f411,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f410,f57])).

fof(f410,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f409,f59])).

fof(f409,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK6(sK0,sK1,sK2)))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f408,f122])).

fof(f248,plain,(
    spl8_23 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl8_23 ),
    inference(subsumption_resolution,[],[f246,f229])).

fof(f229,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl8_23
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f237,plain,(
    spl8_22 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl8_22 ),
    inference(subsumption_resolution,[],[f235,f225])).

fof(f225,plain,
    ( ~ l1_struct_0(sK1)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl8_22
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f234,plain,
    ( ~ spl8_22
    | ~ spl8_23
    | spl8_24
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f221,f124,f231,f227,f223])).

fof(f221,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl8_2 ),
    inference(resolution,[],[f109,f125])).

fof(f215,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f124,f120])).

fof(f62,plain,
    ( r1_tsep_1(sK1,sK2)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f214,plain,
    ( spl8_1
    | spl8_21 ),
    inference(avatar_split_clause,[],[f63,f212,f120])).

fof(f63,plain,(
    ! [X6,X8,X7] :
      ( v1_funct_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,sK2,X6)
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,sK1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f210,plain,
    ( spl8_1
    | spl8_20 ),
    inference(avatar_split_clause,[],[f64,f208,f120])).

fof(f64,plain,(
    ! [X6,X8,X7] :
      ( v1_funct_2(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,sK2,X6)
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,sK1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f206,plain,
    ( spl8_1
    | spl8_19 ),
    inference(avatar_split_clause,[],[f65,f204,f120])).

fof(f65,plain,(
    ! [X6,X8,X7] :
      ( v5_pre_topc(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_tsep_1(sK0,sK1,sK2),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,sK2,X6)
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,sK1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f202,plain,
    ( spl8_1
    | spl8_18 ),
    inference(avatar_split_clause,[],[f66,f200,f120])).

fof(f66,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(k10_tmap_1(sK0,X6,sK1,sK2,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X6))))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,sK2,X6)
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,sK1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(sK1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f198,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f67,f195,f124,f120])).

fof(f67,plain,
    ( ~ v2_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f193,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_16 ),
    inference(avatar_split_clause,[],[f68,f190,f124,f120])).

fof(f68,plain,
    ( v2_pre_topc(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f188,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_15 ),
    inference(avatar_split_clause,[],[f69,f185,f124,f120])).

fof(f69,plain,
    ( l1_pre_topc(sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f183,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_14 ),
    inference(avatar_split_clause,[],[f70,f180,f124,f120])).

fof(f70,plain,
    ( v1_funct_1(sK4)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f178,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_13 ),
    inference(avatar_split_clause,[],[f71,f175,f124,f120])).

fof(f71,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f173,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_12 ),
    inference(avatar_split_clause,[],[f72,f170,f124,f120])).

fof(f72,plain,
    ( v5_pre_topc(sK4,sK1,sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f168,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_11 ),
    inference(avatar_split_clause,[],[f73,f165,f124,f120])).

fof(f73,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f163,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_10 ),
    inference(avatar_split_clause,[],[f74,f160,f124,f120])).

fof(f74,plain,
    ( v1_funct_1(sK5)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f158,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_9 ),
    inference(avatar_split_clause,[],[f75,f155,f124,f120])).

fof(f75,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f153,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_8 ),
    inference(avatar_split_clause,[],[f76,f150,f124,f120])).

fof(f76,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f148,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_7 ),
    inference(avatar_split_clause,[],[f77,f145,f124,f120])).

fof(f77,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tsep_1(sK1,sK2)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1813+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:38 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  533 (3617 expanded)
%              Number of leaves         :   52 (1444 expanded)
%              Depth                    :   61
%              Number of atoms          : 4149 (114531 expanded)
%              Number of equality atoms :   89 ( 134 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3815,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f209,f215,f231,f367,f401,f404,f407,f436,f2295,f2327,f2336,f2442,f2451,f2490,f2513,f2530,f2554,f2559,f2582,f2598,f2622,f2626,f2651,f2674,f2679,f2683,f2692,f2706,f3012,f3052,f3058,f3160,f3814])).

fof(f3814,plain,
    ( ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(avatar_contradiction_clause,[],[f3813])).

fof(f3813,plain,
    ( $false
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3812,f75])).

fof(f75,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
      | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
      | ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
      | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
      | ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
      | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
      | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) )
    & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        & v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
        & v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
        & v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
        & m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        & v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
        & v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        & v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7)) )
      | ( m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
        & v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
        & v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
        & v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) ) )
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK9)
    & r4_tsep_1(sK5,sK7,sK8)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f52,f57,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                          | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & r4_tsep_1(X0,X2,X3)
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK5,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK5,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK5,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK5,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(sK5,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK5,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK5,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK5,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(sK5,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK5,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK5,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK5,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(sK5,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK5,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(sK5,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK5,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(sK5,X2,X3)
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

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK5,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK5,X1,X4,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK5,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK5,X1,X4,X3))
                      | ~ m1_subset_1(k2_tmap_1(sK5,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK5,X1,X4,X2),X2,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK5,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK5,X1,X4,X2))
                      | ~ m1_subset_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),X1)
                      | ~ v1_funct_2(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3))) )
                    & ( ( m1_subset_1(k2_tmap_1(sK5,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK5,X1,X4,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK5,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK5,X1,X4,X3))
                        & m1_subset_1(k2_tmap_1(sK5,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK5,X1,X4,X2),X2,X1)
                        & v1_funct_2(k2_tmap_1(sK5,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK5,X1,X4,X2)) )
                      | ( m1_subset_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),X1)
                        & v1_funct_2(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK5,X1,X4,k1_tsep_1(sK5,X2,X3))) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & r4_tsep_1(sK5,X2,X3)
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
                  ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                    | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X2),X2,sK6)
                    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,X2),u1_struct_0(X2),u1_struct_0(sK6))
                    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,X2))
                    | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))))
                    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),sK6)
                    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))
                    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3))) )
                  & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                      & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                      & v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                      & v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                      & m1_subset_1(k2_tmap_1(sK5,sK6,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                      & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X2),X2,sK6)
                      & v1_funct_2(k2_tmap_1(sK5,sK6,X4,X2),u1_struct_0(X2),u1_struct_0(sK6))
                      & v1_funct_1(k2_tmap_1(sK5,sK6,X4,X2)) )
                    | ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))))
                      & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),sK6)
                      & v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))
                      & v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3))) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                  & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK6))
                  & v1_funct_1(X4) )
              & r4_tsep_1(sK5,X2,X3)
              & m1_pre_topc(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                  | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                  | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                  | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                  | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                  | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X2),X2,sK6)
                  | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,X2),u1_struct_0(X2),u1_struct_0(sK6))
                  | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,X2))
                  | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))))
                  | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),sK6)
                  | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))
                  | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3))) )
                & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                    & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                    & v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                    & v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                    & m1_subset_1(k2_tmap_1(sK5,sK6,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                    & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X2),X2,sK6)
                    & v1_funct_2(k2_tmap_1(sK5,sK6,X4,X2),u1_struct_0(X2),u1_struct_0(sK6))
                    & v1_funct_1(k2_tmap_1(sK5,sK6,X4,X2)) )
                  | ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))))
                    & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),k1_tsep_1(sK5,X2,X3),sK6)
                    & v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3)),u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(sK6))
                    & v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,X2,X3))) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
                & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK6))
                & v1_funct_1(X4) )
            & r4_tsep_1(sK5,X2,X3)
            & m1_pre_topc(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
                | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
                | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
                | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7))
                | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))))
                | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_tsep_1(sK5,sK7,X3),sK6)
                | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))
                | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3))) )
              & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                  & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                  & v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                  & v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                  & m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
                  & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
                  & v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
                  & v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7)) )
                | ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))))
                  & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_tsep_1(sK5,sK7,X3),sK6)
                  & v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))
                  & v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3))) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
              & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK6))
              & v1_funct_1(X4) )
          & r4_tsep_1(sK5,sK7,X3)
          & m1_pre_topc(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
              | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
              | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
              | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
              | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
              | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
              | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
              | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7))
              | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))))
              | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_tsep_1(sK5,sK7,X3),sK6)
              | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))
              | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3))) )
            & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,X3),X3,sK6)
                & v1_funct_2(k2_tmap_1(sK5,sK6,X4,X3),u1_struct_0(X3),u1_struct_0(sK6))
                & v1_funct_1(k2_tmap_1(sK5,sK6,X4,X3))
                & m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
                & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
                & v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
                & v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7)) )
              | ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))))
                & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),k1_tsep_1(sK5,sK7,X3),sK6)
                & v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3)),u1_struct_0(k1_tsep_1(sK5,sK7,X3)),u1_struct_0(sK6))
                & v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,X3))) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
            & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK6))
            & v1_funct_1(X4) )
        & r4_tsep_1(sK5,sK7,X3)
        & m1_pre_topc(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
            | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK8),sK8,sK6)
            | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
            | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK8))
            | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
            | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
            | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
            | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7))
            | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
            | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
            | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
            | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8))) )
          & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
              & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK8),sK8,sK6)
              & v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
              & v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK8))
              & m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
              & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
              & v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
              & v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7)) )
            | ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
              & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
              & v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
              & v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8))) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK6))
          & v1_funct_1(X4) )
      & r4_tsep_1(sK5,sK7,sK8)
      & m1_pre_topc(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
          | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK8),sK8,sK6)
          | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
          | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK8))
          | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
          | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
          | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
          | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7))
          | ~ m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
          | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
          | ~ v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
          | ~ v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8))) )
        & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
            & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK8),sK8,sK6)
            & v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
            & v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK8))
            & m1_subset_1(k2_tmap_1(sK5,sK6,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
            & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,sK7),sK7,sK6)
            & v1_funct_2(k2_tmap_1(sK5,sK6,X4,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
            & v1_funct_1(k2_tmap_1(sK5,sK6,X4,sK7)) )
          | ( m1_subset_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
            & v5_pre_topc(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
            & v1_funct_2(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
            & v1_funct_1(k2_tmap_1(sK5,sK6,X4,k1_tsep_1(sK5,sK7,sK8))) ) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK6))
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) )
      & ( ( m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
          & v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
          & v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
          & v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
          & m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
          & v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
          & v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
          & v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7)) )
        | ( m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
          & v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
          & v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
          & v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) ) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      & v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                   => ( r4_tsep_1(X0,X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                              & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f3812,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3811,f80])).

fof(f80,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f3811,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3810,f82])).

fof(f82,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f3810,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3809,f83])).

fof(f83,plain,(
    r4_tsep_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f3809,plain,
    ( ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(resolution,[],[f3804,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r4_tsep_1(X0,X1,X2)
       => r4_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r4_tsep_1)).

fof(f3804,plain,
    ( ~ r4_tsep_1(sK5,sK8,sK7)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3803,f79])).

fof(f79,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f3803,plain,
    ( ~ r4_tsep_1(sK5,sK8,sK7)
    | v2_struct_0(sK7)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3802,f80])).

fof(f3802,plain,
    ( ~ r4_tsep_1(sK5,sK8,sK7)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | ~ spl10_33
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3801,f2276])).

fof(f2276,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f2275])).

fof(f2275,plain,
    ( spl10_33
  <=> m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f3801,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ r4_tsep_1(sK5,sK8,sK7)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_30
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3800,f2264])).

fof(f2264,plain,
    ( m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f2263,plain,
    ( spl10_30
  <=> m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f3800,plain,
    ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ r4_tsep_1(sK5,sK8,sK7)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ spl10_3
    | spl10_11
    | spl10_34
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3793,f2280])).

fof(f2280,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | spl10_34 ),
    inference(avatar_component_clause,[],[f2279])).

fof(f2279,plain,
    ( spl10_34
  <=> v2_struct_0(k1_tsep_1(sK5,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f3793,plain,
    ( v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ r4_tsep_1(sK5,sK8,sK7)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ spl10_3
    | spl10_11
    | ~ spl10_40
    | ~ spl10_47 ),
    inference(resolution,[],[f3774,f2569])).

fof(f2569,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2568,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f2568,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK5)
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2567,f75])).

fof(f2567,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2566,f79])).

fof(f2566,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2565,f80])).

fof(f2565,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2564,f81])).

fof(f81,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f2564,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2563,f82])).

fof(f2563,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2561,f2544])).

fof(f2544,plain,
    ( sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f2543])).

fof(f2543,plain,
    ( spl10_40
  <=> sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f2561,plain,
    ( sP0(sK6,sK7,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_3 ),
    inference(resolution,[],[f171,f1330])).

fof(f1330,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(X3,X4,X5,k1_tsep_1(X0,X2,X1)),k1_tsep_1(X0,X2,X1),X4)
      | sP0(X4,X2,X1,X0,k2_tmap_1(X3,X4,X5,k1_tsep_1(X0,X2,X1)))
      | ~ sP3(X4,k1_tsep_1(X0,X2,X1),X5,X3)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f461,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f461,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ v5_pre_topc(k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)),k1_tsep_1(X8,X7,X6),X5)
      | sP0(X5,X6,X7,X8,k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)))
      | ~ sP3(X5,k1_tsep_1(X8,X7,X6),X10,X9) ) ),
    inference(subsumption_resolution,[],[f460,f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP3(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP3(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f460,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( sP0(X5,X6,X7,X8,k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)))
      | ~ v5_pre_topc(k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)),k1_tsep_1(X8,X7,X6),X5)
      | ~ v1_funct_1(k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)))
      | ~ sP3(X5,k1_tsep_1(X8,X7,X6),X10,X9) ) ),
    inference(subsumption_resolution,[],[f453,f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f453,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( sP0(X5,X6,X7,X8,k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)))
      | ~ v5_pre_topc(k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)),k1_tsep_1(X8,X7,X6),X5)
      | ~ v1_funct_2(k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)),u1_struct_0(k1_tsep_1(X8,X7,X6)),u1_struct_0(X5))
      | ~ v1_funct_1(k2_tmap_1(X9,X5,X10,k1_tsep_1(X8,X7,X6)))
      | ~ sP3(X5,k1_tsep_1(X8,X7,X6),X10,X9) ) ),
    inference(resolution,[],[f135,f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f171,plain,
    ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl10_3
  <=> v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f3774,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,X0,sK8)))
        | v2_struct_0(k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(k1_tsep_1(sK5,X0,sK8),sK5)
        | ~ r4_tsep_1(sK5,sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3773,f73])).

fof(f3773,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,X0,sK8)))
        | v2_struct_0(k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(k1_tsep_1(sK5,X0,sK8),sK5)
        | ~ r4_tsep_1(sK5,sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3772,f75])).

fof(f3772,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,X0,sK8)))
        | v2_struct_0(k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(k1_tsep_1(sK5,X0,sK8),sK5)
        | ~ r4_tsep_1(sK5,sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3771,f81])).

fof(f3771,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,X0,sK8)))
        | v2_struct_0(k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(k1_tsep_1(sK5,X0,sK8),sK5)
        | ~ r4_tsep_1(sK5,sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3765,f82])).

fof(f3765,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,X0,sK8)))
        | v2_struct_0(k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(k1_tsep_1(sK5,X0,sK8),sK5)
        | ~ r4_tsep_1(sK5,sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(duplicate_literal_removal,[],[f3762])).

fof(f3762,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,X0,sK8)))
        | v2_struct_0(k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,X0,sK8))
        | ~ m1_pre_topc(k1_tsep_1(sK5,X0,sK8),sK5)
        | ~ r4_tsep_1(sK5,sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(superposition,[],[f3752,f141])).

fof(f3752,plain,
    ( ! [X1] :
        ( ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3751,f73])).

fof(f3751,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3750,f74])).

fof(f74,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f3750,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3749,f75])).

fof(f3749,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3748,f76])).

fof(f76,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f3748,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3747,f77])).

fof(f77,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f3747,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3746,f78])).

fof(f78,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f3746,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3745,f81])).

fof(f3745,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3740,f82])).

fof(f3740,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(duplicate_literal_removal,[],[f3737])).

fof(f3737,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)))
        | ~ r4_tsep_1(sK5,sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(resolution,[],[f3666,f607])).

fof(f607,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X1,X3,X4,X2,X0)
      | ~ sP0(X1,X3,X2,X0,X4)
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
    inference(subsumption_resolution,[],[f606,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f606,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X1,X3,X4,X2,X0)
      | ~ sP0(X1,X3,X2,X0,X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(subsumption_resolution,[],[f605,f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f605,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X1,X3,X4,X2,X0)
      | ~ sP0(X1,X3,X2,X0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(subsumption_resolution,[],[f136,f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f136,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X1,X3,X4,X2,X0)
      | ~ sP0(X1,X3,X2,X0,X4)
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
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(definition_folding,[],[f21,f43,f42])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f3666,plain,
    ( ! [X1] :
        ( ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3665,f73])).

fof(f3665,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3664,f74])).

fof(f3664,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3663,f75])).

fof(f3663,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3662,f76])).

fof(f3662,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3661,f77])).

fof(f3661,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3660,f78])).

fof(f3660,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3650,f82])).

fof(f3650,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ m1_pre_topc(sK8,sK5)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(duplicate_literal_removal,[],[f3645])).

fof(f3645,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X1))
        | ~ sP1(sK6,X1,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1)),sK8,sK5)
        | ~ m1_pre_topc(sK8,sK5)
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X1),sK5)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK6,X1,sK8,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X1))) )
    | spl10_11
    | ~ spl10_47 ),
    inference(resolution,[],[f3632,f508])).

fof(f508,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( sP4(X6,X7,X8,k1_tsep_1(X9,X10,X11),X12)
      | ~ m1_pre_topc(X7,X12)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,X11),X12)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP0(X6,X11,X10,X9,X8) ) ),
    inference(subsumption_resolution,[],[f507,f132])).

fof(f507,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( sP4(X6,X7,X8,k1_tsep_1(X9,X10,X11),X12)
      | ~ v1_funct_2(X8,u1_struct_0(k1_tsep_1(X9,X10,X11)),u1_struct_0(X6))
      | ~ m1_pre_topc(X7,X12)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,X11),X12)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP0(X6,X11,X10,X9,X8) ) ),
    inference(subsumption_resolution,[],[f486,f131])).

fof(f486,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( sP4(X6,X7,X8,k1_tsep_1(X9,X10,X11),X12)
      | ~ v1_funct_2(X8,u1_struct_0(k1_tsep_1(X9,X10,X11)),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X7,X12)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,X11),X12)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP0(X6,X11,X10,X9,X8) ) ),
    inference(resolution,[],[f158,f134])).

fof(f158,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP4(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP4(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f41,f49])).

fof(f49,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP4(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f3632,plain,
    ( ! [X19] :
        ( ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X19)),k1_tsep_1(sK5,sK8,X19),sK5)
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X19))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X19),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X19))
        | ~ sP1(sK6,X19,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X19)),sK8,sK5) )
    | spl10_11
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3581,f204])).

fof(f204,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl10_11
  <=> v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f3581,plain,
    ( ! [X19] :
        ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
        | ~ sP1(sK6,X19,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X19)),sK8,sK5)
        | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK8,X19))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK8,X19),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK8,X19))
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK8,X19)),k1_tsep_1(sK5,sK8,X19),sK5) )
    | ~ spl10_47 ),
    inference(superposition,[],[f124,f3555])).

fof(f3555,plain,
    ( ! [X0] :
        ( k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3554,f155])).

fof(f155,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP4(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f3554,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f3549,f156])).

fof(f156,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f3549,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_47 ),
    inference(resolution,[],[f2804,f157])).

fof(f157,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f2804,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2803,f73])).

fof(f2803,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2802,f74])).

fof(f2802,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2801,f75])).

fof(f2801,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2800,f76])).

fof(f2800,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2799,f77])).

fof(f2799,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2798,f78])).

fof(f2798,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2797,f81])).

fof(f2797,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2796,f82])).

fof(f2796,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2795,f84])).

fof(f84,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f58])).

fof(f2795,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2794,f85])).

fof(f85,plain,(
    v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f58])).

fof(f2794,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f2793,f86])).

fof(f86,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f2793,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_47 ),
    inference(resolution,[],[f2636,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f2636,plain,
    ( ! [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X2,k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X2 )
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f2635])).

fof(f2635,plain,
    ( spl10_47
  <=> ! [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X2,k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f3160,plain,
    ( spl10_41
    | ~ spl10_35
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f3159,f2543,f2283,f2547])).

fof(f2547,plain,
    ( spl10_41
  <=> sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f2283,plain,
    ( spl10_35
  <=> sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f3159,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ spl10_35
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f3158,f2544])).

fof(f3158,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3157,f73])).

fof(f3157,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3156,f74])).

fof(f3156,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3155,f75])).

fof(f3155,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3154,f76])).

fof(f3154,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3153,f77])).

fof(f3153,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3152,f78])).

fof(f3152,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3151,f79])).

fof(f3151,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3150,f80])).

fof(f3150,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3149,f81])).

fof(f3149,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3148,f82])).

fof(f3148,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f3147,f83])).

fof(f3147,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(resolution,[],[f2285,f642])).

fof(f642,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ sP1(X5,X6,k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)),X10,X9)
      | sP0(X5,X6,X10,X9,k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)))
      | ~ r4_tsep_1(X9,X10,X6)
      | ~ m1_pre_topc(X6,X9)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP3(X5,k1_tsep_1(X9,X10,X6),X8,X7) ) ),
    inference(subsumption_resolution,[],[f641,f147])).

fof(f641,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ sP1(X5,X6,k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)),X10,X9)
      | sP0(X5,X6,X10,X9,k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)))
      | ~ v1_funct_1(k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)))
      | ~ r4_tsep_1(X9,X10,X6)
      | ~ m1_pre_topc(X6,X9)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP3(X5,k1_tsep_1(X9,X10,X6),X8,X7) ) ),
    inference(subsumption_resolution,[],[f632,f148])).

fof(f632,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ sP1(X5,X6,k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)),X10,X9)
      | sP0(X5,X6,X10,X9,k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)))
      | ~ v1_funct_2(k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)),u1_struct_0(k1_tsep_1(X9,X10,X6)),u1_struct_0(X5))
      | ~ v1_funct_1(k2_tmap_1(X7,X5,X8,k1_tsep_1(X9,X10,X6)))
      | ~ r4_tsep_1(X9,X10,X6)
      | ~ m1_pre_topc(X6,X9)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP3(X5,k1_tsep_1(X9,X10,X6),X8,X7) ) ),
    inference(resolution,[],[f137,f149])).

fof(f137,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f2285,plain,
    ( sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f2283])).

fof(f3058,plain,
    ( spl10_41
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f3057,f2543,f170,f2547])).

fof(f3057,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2562,f2544])).

fof(f2562,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_3 ),
    inference(resolution,[],[f171,f461])).

fof(f3052,plain,
    ( ~ spl10_41
    | spl10_35 ),
    inference(avatar_split_clause,[],[f3051,f2283,f2547])).

fof(f3051,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3050,f73])).

fof(f3050,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3049,f74])).

fof(f3049,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3048,f75])).

fof(f3048,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3047,f76])).

fof(f3047,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3046,f77])).

fof(f3046,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3045,f78])).

fof(f3045,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3044,f79])).

fof(f3044,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3043,f80])).

fof(f3043,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3042,f81])).

fof(f3042,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3041,f82])).

fof(f3041,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(subsumption_resolution,[],[f3018,f83])).

fof(f3018,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_35 ),
    inference(resolution,[],[f2284,f607])).

fof(f2284,plain,
    ( ~ sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | spl10_35 ),
    inference(avatar_component_clause,[],[f2283])).

fof(f3012,plain,
    ( ~ spl10_35
    | spl10_7
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33
    | spl10_34
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f2964,f2607,f2279,f2275,f2271,f2267,f186,f2283])).

fof(f186,plain,
    ( spl10_7
  <=> v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f2267,plain,
    ( spl10_31
  <=> sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f2271,plain,
    ( spl10_32
  <=> m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f2607,plain,
    ( spl10_43
  <=> ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X1,k2_tmap_1(sK5,sK6,sK9,sK7))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f2964,plain,
    ( ~ sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | spl10_7
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33
    | spl10_34
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2963,f2280])).

fof(f2963,plain,
    ( v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | spl10_7
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2962,f2276])).

fof(f2962,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | spl10_7
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2946,f2272])).

fof(f2272,plain,
    ( m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f2271])).

fof(f2946,plain,
    ( ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | spl10_7
    | ~ spl10_31
    | ~ spl10_43 ),
    inference(resolution,[],[f2907,f2268])).

fof(f2268,plain,
    ( sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f2267])).

fof(f2907,plain,
    ( ! [X19] :
        ( ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X19)),k1_tsep_1(sK5,sK7,X19),sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X19))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X19),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK7,X19))
        | ~ sP1(sK6,X19,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X19)),sK7,sK5) )
    | spl10_7
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2858,f188])).

fof(f188,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f2858,plain,
    ( ! [X19] :
        ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
        | ~ sP1(sK6,X19,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X19)),sK7,sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X19))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X19),sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK7,X19))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X19)),k1_tsep_1(sK5,sK7,X19),sK5) )
    | ~ spl10_43 ),
    inference(superposition,[],[f124,f2832])).

fof(f2832,plain,
    ( ! [X0] :
        ( k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2831,f155])).

fof(f2831,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2826,f156])).

fof(f2826,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_43 ),
    inference(resolution,[],[f2790,f157])).

fof(f2790,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2789,f73])).

fof(f2789,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2788,f74])).

fof(f2788,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2787,f75])).

fof(f2787,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2786,f76])).

fof(f2786,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2785,f77])).

fof(f2785,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2784,f78])).

fof(f2784,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2783,f79])).

fof(f2783,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2782,f80])).

fof(f2782,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2781,f84])).

fof(f2781,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2780,f85])).

fof(f2780,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2779,f86])).

fof(f2779,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl10_43 ),
    inference(resolution,[],[f2608,f138])).

fof(f2608,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X1,k2_tmap_1(sK5,sK6,sK9,sK7))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X1 )
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f2607])).

fof(f2706,plain,
    ( spl10_47
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f2705,f206,f198,f194,f2635])).

fof(f194,plain,
    ( spl10_9
  <=> v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f198,plain,
    ( spl10_10
  <=> v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f206,plain,
    ( spl10_12
  <=> m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f2705,plain,
    ( ! [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X3,k2_tmap_1(sK5,sK6,sK9,sK8))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(X3) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f2704,f195])).

fof(f195,plain,
    ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f2704,plain,
    ( ! [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X3,k2_tmap_1(sK5,sK6,sK9,sK8))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X3
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(X3) )
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f2695,f199])).

fof(f199,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f2695,plain,
    ( ! [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X3,k2_tmap_1(sK5,sK6,sK9,sK8))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X3
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(X3) )
    | ~ spl10_12 ),
    inference(resolution,[],[f207,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f207,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f2692,plain,
    ( spl10_6
    | ~ spl10_15
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f2691])).

fof(f2691,plain,
    ( $false
    | spl10_6
    | ~ spl10_15
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f2690,f372])).

fof(f372,plain,
    ( l1_struct_0(sK7)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl10_16
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f2690,plain,
    ( ~ l1_struct_0(sK7)
    | spl10_6
    | ~ spl10_15 ),
    inference(resolution,[],[f2689,f366])).

fof(f366,plain,
    ( ! [X0] :
        ( sP3(sK6,X0,sK9,sK5)
        | ~ l1_struct_0(X0) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl10_15
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | sP3(sK6,X0,sK9,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f2689,plain,
    ( ~ sP3(sK6,sK7,sK9,sK5)
    | spl10_6 ),
    inference(resolution,[],[f184,f148])).

fof(f184,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl10_6
  <=> v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f2683,plain,
    ( ~ spl10_6
    | spl10_43
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f2682,f190,f178,f2607,f182])).

fof(f178,plain,
    ( spl10_5
  <=> v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f190,plain,
    ( spl10_8
  <=> m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f2682,plain,
    ( ! [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X3,k2_tmap_1(sK5,sK6,sK9,sK7))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X3
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(X3) )
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f2654,f179])).

fof(f179,plain,
    ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f178])).

fof(f2654,plain,
    ( ! [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X3,k2_tmap_1(sK5,sK6,sK9,sK7))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X3
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(X3) )
    | ~ spl10_8 ),
    inference(resolution,[],[f191,f151])).

fof(f191,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f2679,plain,
    ( spl10_10
    | ~ spl10_15
    | ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f2678])).

fof(f2678,plain,
    ( $false
    | spl10_10
    | ~ spl10_15
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f2677,f382])).

fof(f382,plain,
    ( l1_struct_0(sK8)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl10_18
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f2677,plain,
    ( ~ l1_struct_0(sK8)
    | spl10_10
    | ~ spl10_15 ),
    inference(resolution,[],[f2676,f366])).

fof(f2676,plain,
    ( ~ sP3(sK6,sK8,sK9,sK5)
    | spl10_10 ),
    inference(resolution,[],[f200,f148])).

fof(f200,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f2674,plain,
    ( spl10_12
    | ~ spl10_15
    | ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f2673])).

fof(f2673,plain,
    ( $false
    | spl10_12
    | ~ spl10_15
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f2672,f382])).

fof(f2672,plain,
    ( ~ l1_struct_0(sK8)
    | spl10_12
    | ~ spl10_15 ),
    inference(resolution,[],[f2671,f366])).

fof(f2671,plain,
    ( ~ sP3(sK6,sK8,sK9,sK5)
    | spl10_12 ),
    inference(resolution,[],[f208,f149])).

fof(f208,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f2651,plain,(
    spl10_9 ),
    inference(avatar_contradiction_clause,[],[f2650])).

fof(f2650,plain,
    ( $false
    | spl10_9 ),
    inference(subsumption_resolution,[],[f2648,f82])).

fof(f2648,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | spl10_9 ),
    inference(resolution,[],[f196,f545])).

fof(f545,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f544,f73])).

fof(f544,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f543,f74])).

fof(f543,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f542,f75])).

fof(f542,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f541,f76])).

fof(f541,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f540,f77])).

fof(f540,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f539,f78])).

fof(f539,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f538,f84])).

fof(f538,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ v1_funct_1(sK9)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f537,f85])).

fof(f537,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f522,f86])).

fof(f522,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK5,sK6,sK9,X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(superposition,[],[f251,f139])).

fof(f139,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f251,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),sK9,X0)) ),
    inference(subsumption_resolution,[],[f248,f84])).

fof(f248,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK6),sK9,X0))
      | ~ v1_funct_1(sK9) ) ),
    inference(resolution,[],[f153,f86])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f196,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | spl10_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f2626,plain,
    ( spl10_8
    | ~ spl10_15
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f2625])).

fof(f2625,plain,
    ( $false
    | spl10_8
    | ~ spl10_15
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f2624,f372])).

fof(f2624,plain,
    ( ~ l1_struct_0(sK7)
    | spl10_8
    | ~ spl10_15 ),
    inference(resolution,[],[f2623,f366])).

fof(f2623,plain,
    ( ~ sP3(sK6,sK7,sK9,sK5)
    | spl10_8 ),
    inference(resolution,[],[f192,f149])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f2622,plain,(
    spl10_5 ),
    inference(avatar_contradiction_clause,[],[f2621])).

fof(f2621,plain,
    ( $false
    | spl10_5 ),
    inference(subsumption_resolution,[],[f2619,f80])).

fof(f2619,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | spl10_5 ),
    inference(resolution,[],[f180,f545])).

fof(f180,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
    | spl10_5 ),
    inference(avatar_component_clause,[],[f178])).

fof(f2598,plain,
    ( spl10_4
    | ~ spl10_40 ),
    inference(avatar_contradiction_clause,[],[f2597])).

fof(f2597,plain,
    ( $false
    | spl10_4
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2586,f2544])).

fof(f2586,plain,
    ( ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_4 ),
    inference(resolution,[],[f176,f149])).

fof(f176,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl10_4
  <=> m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f2582,plain,
    ( spl10_2
    | ~ spl10_40 ),
    inference(avatar_contradiction_clause,[],[f2581])).

fof(f2581,plain,
    ( $false
    | spl10_2
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f2572,f2544])).

fof(f2572,plain,
    ( ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_2 ),
    inference(resolution,[],[f168,f148])).

fof(f168,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl10_2
  <=> v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2559,plain,
    ( ~ spl10_15
    | ~ spl10_33
    | spl10_40 ),
    inference(avatar_contradiction_clause,[],[f2558])).

fof(f2558,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_33
    | spl10_40 ),
    inference(subsumption_resolution,[],[f2557,f2339])).

fof(f2339,plain,
    ( l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2338,f75])).

fof(f2338,plain,
    ( l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ l1_pre_topc(sK5)
    | ~ spl10_33 ),
    inference(resolution,[],[f2276,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2557,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_15
    | spl10_40 ),
    inference(resolution,[],[f2556,f120])).

fof(f120,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2556,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_15
    | spl10_40 ),
    inference(resolution,[],[f2545,f366])).

fof(f2545,plain,
    ( ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_40 ),
    inference(avatar_component_clause,[],[f2543])).

fof(f2554,plain,
    ( spl10_1
    | ~ spl10_33 ),
    inference(avatar_contradiction_clause,[],[f2553])).

fof(f2553,plain,
    ( $false
    | spl10_1
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2551,f2276])).

fof(f2551,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | spl10_1 ),
    inference(resolution,[],[f164,f545])).

fof(f164,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_1
  <=> v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f2530,plain,
    ( spl10_3
    | ~ spl10_15
    | ~ spl10_33
    | ~ spl10_35 ),
    inference(avatar_contradiction_clause,[],[f2529])).

fof(f2529,plain,
    ( $false
    | spl10_3
    | ~ spl10_15
    | ~ spl10_33
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2528,f2339])).

fof(f2528,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | spl10_3
    | ~ spl10_15
    | ~ spl10_35 ),
    inference(resolution,[],[f2527,f120])).

fof(f2527,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | spl10_3
    | ~ spl10_15
    | ~ spl10_35 ),
    inference(resolution,[],[f2526,f366])).

fof(f2526,plain,
    ( ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2525,f73])).

fof(f2525,plain,
    ( v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2524,f74])).

fof(f2524,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2523,f75])).

fof(f2523,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2522,f76])).

fof(f2522,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2521,f77])).

fof(f2521,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2520,f78])).

fof(f2520,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2519,f79])).

fof(f2519,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2518,f80])).

fof(f2518,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2517,f81])).

fof(f2517,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2516,f82])).

fof(f2516,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2515,f83])).

fof(f2515,plain,
    ( ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_3
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f2514,f247])).

fof(f247,plain,
    ( ~ sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | spl10_3 ),
    inference(resolution,[],[f133,f172])).

fof(f172,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f2514,plain,
    ( sP0(sK6,sK8,sK7,sK5,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)))
    | ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_35 ),
    inference(resolution,[],[f2285,f642])).

fof(f2513,plain,(
    ~ spl10_34 ),
    inference(avatar_contradiction_clause,[],[f2512])).

fof(f2512,plain,
    ( $false
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f2511,f73])).

fof(f2511,plain,
    ( v2_struct_0(sK5)
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f2510,f75])).

fof(f2510,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f2509,f81])).

fof(f2509,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f2508,f82])).

fof(f2508,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f2507,f79])).

fof(f2507,plain,
    ( v2_struct_0(sK7)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f2505,f80])).

fof(f2505,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl10_34 ),
    inference(resolution,[],[f2281,f337])).

fof(f337,plain,(
    ! [X59,X60,X58] :
      ( ~ v2_struct_0(k1_tsep_1(X58,X60,X59))
      | ~ m1_pre_topc(X60,X58)
      | v2_struct_0(X60)
      | ~ m1_pre_topc(X59,X58)
      | v2_struct_0(X59)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X58) ) ),
    inference(subsumption_resolution,[],[f305,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f305,plain,(
    ! [X59,X60,X58] :
      ( ~ v2_struct_0(k1_tsep_1(X58,X60,X59))
      | ~ sP2(X58,X60,X59)
      | ~ m1_pre_topc(X60,X58)
      | v2_struct_0(X60)
      | ~ m1_pre_topc(X59,X58)
      | v2_struct_0(X59)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X58) ) ),
    inference(superposition,[],[f142,f141])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f2281,plain,
    ( v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f2279])).

fof(f2490,plain,
    ( ~ spl10_15
    | ~ spl10_33
    | spl10_36 ),
    inference(avatar_contradiction_clause,[],[f2489])).

fof(f2489,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2488,f2339])).

fof(f2488,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_15
    | ~ spl10_33
    | spl10_36 ),
    inference(resolution,[],[f2487,f120])).

fof(f2487,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_15
    | ~ spl10_33
    | spl10_36 ),
    inference(resolution,[],[f2486,f366])).

fof(f2486,plain,
    ( ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2485,f73])).

fof(f2485,plain,
    ( v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2484,f74])).

fof(f2484,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2483,f75])).

fof(f2483,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2482,f76])).

fof(f2482,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2481,f77])).

fof(f2481,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2480,f78])).

fof(f2480,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | ~ spl10_33
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2479,f2276])).

fof(f2479,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f2477,f82])).

fof(f2477,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_36 ),
    inference(resolution,[],[f2294,f510])).

fof(f510,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( sP4(X13,X14,k2_tmap_1(X15,X13,X16,X17),X17,X18)
      | ~ m1_pre_topc(X14,X18)
      | ~ m1_pre_topc(X17,X18)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP3(X13,X17,X16,X15) ) ),
    inference(subsumption_resolution,[],[f509,f147])).

fof(f509,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( sP4(X13,X14,k2_tmap_1(X15,X13,X16,X17),X17,X18)
      | ~ v1_funct_1(k2_tmap_1(X15,X13,X16,X17))
      | ~ m1_pre_topc(X14,X18)
      | ~ m1_pre_topc(X17,X18)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP3(X13,X17,X16,X15) ) ),
    inference(subsumption_resolution,[],[f487,f148])).

fof(f487,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( sP4(X13,X14,k2_tmap_1(X15,X13,X16,X17),X17,X18)
      | ~ v1_funct_2(k2_tmap_1(X15,X13,X16,X17),u1_struct_0(X17),u1_struct_0(X13))
      | ~ v1_funct_1(k2_tmap_1(X15,X13,X16,X17))
      | ~ m1_pre_topc(X14,X18)
      | ~ m1_pre_topc(X17,X18)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP3(X13,X17,X16,X15) ) ),
    inference(resolution,[],[f158,f149])).

fof(f2294,plain,
    ( ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f2292])).

fof(f2292,plain,
    ( spl10_36
  <=> sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f2451,plain,(
    spl10_32 ),
    inference(avatar_contradiction_clause,[],[f2450])).

fof(f2450,plain,
    ( $false
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2449,f73])).

fof(f2449,plain,
    ( v2_struct_0(sK5)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2448,f74])).

fof(f2448,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2447,f75])).

fof(f2447,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2446,f79])).

fof(f2446,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2445,f80])).

fof(f2445,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2444,f81])).

fof(f2444,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f2443,f82])).

fof(f2443,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_32 ),
    inference(resolution,[],[f2273,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f2273,plain,
    ( ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | spl10_32 ),
    inference(avatar_component_clause,[],[f2271])).

fof(f2442,plain,
    ( ~ spl10_15
    | spl10_31
    | ~ spl10_33 ),
    inference(avatar_contradiction_clause,[],[f2441])).

fof(f2441,plain,
    ( $false
    | ~ spl10_15
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2440,f2339])).

fof(f2440,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_15
    | spl10_31
    | ~ spl10_33 ),
    inference(resolution,[],[f2439,f120])).

fof(f2439,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ spl10_15
    | spl10_31
    | ~ spl10_33 ),
    inference(resolution,[],[f2438,f366])).

fof(f2438,plain,
    ( ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2437,f73])).

fof(f2437,plain,
    ( v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2436,f74])).

fof(f2436,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2435,f75])).

fof(f2435,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2434,f76])).

fof(f2434,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2433,f77])).

fof(f2433,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2432,f78])).

fof(f2432,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f2431,f2276])).

fof(f2431,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31 ),
    inference(subsumption_resolution,[],[f2429,f80])).

fof(f2429,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP3(sK6,k1_tsep_1(sK5,sK7,sK8),sK9,sK5)
    | spl10_31 ),
    inference(resolution,[],[f2269,f510])).

fof(f2269,plain,
    ( ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | spl10_31 ),
    inference(avatar_component_clause,[],[f2267])).

fof(f2336,plain,(
    spl10_30 ),
    inference(avatar_contradiction_clause,[],[f2335])).

fof(f2335,plain,
    ( $false
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2334,f73])).

fof(f2334,plain,
    ( v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2333,f74])).

fof(f2333,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2332,f75])).

fof(f2332,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2331,f81])).

fof(f2331,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2330,f82])).

fof(f2330,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2329,f79])).

fof(f2329,plain,
    ( v2_struct_0(sK7)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(subsumption_resolution,[],[f2328,f80])).

fof(f2328,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_30 ),
    inference(resolution,[],[f2265,f334])).

fof(f334,plain,(
    ! [X57,X56,X55] :
      ( m1_pre_topc(X56,k1_tsep_1(X55,X57,X56))
      | ~ m1_pre_topc(X57,X55)
      | v2_struct_0(X57)
      | ~ m1_pre_topc(X56,X55)
      | v2_struct_0(X56)
      | ~ l1_pre_topc(X55)
      | ~ v2_pre_topc(X55)
      | v2_struct_0(X55) ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X57,X56,X55] :
      ( m1_pre_topc(X56,k1_tsep_1(X55,X57,X56))
      | ~ m1_pre_topc(X57,X55)
      | v2_struct_0(X57)
      | ~ m1_pre_topc(X56,X55)
      | v2_struct_0(X56)
      | ~ l1_pre_topc(X55)
      | ~ v2_pre_topc(X55)
      | v2_struct_0(X55)
      | ~ m1_pre_topc(X56,X55)
      | v2_struct_0(X56)
      | ~ m1_pre_topc(X57,X55)
      | v2_struct_0(X57)
      | ~ l1_pre_topc(X55)
      | v2_struct_0(X55) ) ),
    inference(superposition,[],[f140,f141])).

fof(f2265,plain,
    ( ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | spl10_30 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f2327,plain,(
    spl10_33 ),
    inference(avatar_contradiction_clause,[],[f2326])).

fof(f2326,plain,
    ( $false
    | spl10_33 ),
    inference(subsumption_resolution,[],[f2325,f73])).

fof(f2325,plain,
    ( v2_struct_0(sK5)
    | spl10_33 ),
    inference(subsumption_resolution,[],[f2324,f75])).

fof(f2324,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_33 ),
    inference(subsumption_resolution,[],[f2323,f81])).

fof(f2323,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_33 ),
    inference(subsumption_resolution,[],[f2322,f82])).

fof(f2322,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_33 ),
    inference(subsumption_resolution,[],[f2321,f79])).

fof(f2321,plain,
    ( v2_struct_0(sK7)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_33 ),
    inference(subsumption_resolution,[],[f2319,f80])).

fof(f2319,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl10_33 ),
    inference(resolution,[],[f2277,f339])).

fof(f339,plain,(
    ! [X66,X64,X65] :
      ( m1_pre_topc(k1_tsep_1(X64,X66,X65),X64)
      | ~ m1_pre_topc(X66,X64)
      | v2_struct_0(X66)
      | ~ m1_pre_topc(X65,X64)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(X64)
      | v2_struct_0(X64) ) ),
    inference(subsumption_resolution,[],[f307,f145])).

fof(f307,plain,(
    ! [X66,X64,X65] :
      ( m1_pre_topc(k1_tsep_1(X64,X66,X65),X64)
      | ~ sP2(X64,X66,X65)
      | ~ m1_pre_topc(X66,X64)
      | v2_struct_0(X66)
      | ~ m1_pre_topc(X65,X64)
      | v2_struct_0(X65)
      | ~ l1_pre_topc(X64)
      | v2_struct_0(X64) ) ),
    inference(superposition,[],[f144,f141])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2277,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | spl10_33 ),
    inference(avatar_component_clause,[],[f2275])).

fof(f2295,plain,
    ( ~ spl10_36
    | ~ spl10_30
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_33
    | spl10_34
    | spl10_35
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f2290,f206,f202,f198,f194,f190,f186,f182,f178,f2283,f2279,f2275,f2271,f2267,f2263,f2292])).

fof(f2290,plain,
    ( sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f2289,f195])).

fof(f2289,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f2288,f199])).

fof(f2288,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f2287,f203])).

fof(f203,plain,
    ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f2287,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f2202,f207])).

fof(f2202,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(duplicate_literal_removal,[],[f2201])).

fof(f2201,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | sP1(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),sK7,sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK8))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,k1_tsep_1(sK5,sK7,sK8))
    | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(superposition,[],[f866,f904])).

fof(f904,plain,
    ( ! [X0] :
        ( k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK5)
        | ~ m1_pre_topc(sK8,X0)
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f903,f155])).

fof(f903,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f900,f156])).

fof(f900,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK8,X0)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK8,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ sP4(sK6,sK8,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(resolution,[],[f690,f157])).

fof(f690,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_pre_topc(sK8,X1)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f689,f73])).

fof(f689,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f688,f74])).

fof(f688,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f687,f75])).

fof(f687,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f686,f76])).

fof(f686,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f685,f77])).

fof(f685,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f684,f78])).

fof(f684,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f683,f81])).

fof(f683,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f682,f82])).

fof(f682,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f681,f84])).

fof(f681,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f680,f85])).

fof(f680,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f668,f86])).

fof(f668,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X1,sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK8,sK5)
        | v2_struct_0(sK8)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK8) = k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1)),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X1,sK8,k2_tmap_1(sK5,sK6,sK9,X1))) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(resolution,[],[f138,f422])).

fof(f422,plain,
    ( ! [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X2,k2_tmap_1(sK5,sK6,sK9,sK8))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(X2) )
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f421,f195])).

fof(f421,plain,
    ( ! [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X2,k2_tmap_1(sK5,sK6,sK9,sK8))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X2
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(X2) )
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f410,f199])).

fof(f410,plain,
    ( ! [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X2,k2_tmap_1(sK5,sK6,sK9,sK8))
        | k2_tmap_1(sK5,sK6,sK9,sK8) = X2
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        | ~ v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK6))
        | ~ v1_funct_1(X2) )
    | ~ spl10_12 ),
    inference(resolution,[],[f151,f207])).

fof(f866,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),X2,sK6)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),u1_struct_0(X2),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))))
        | sP1(sK6,X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),sK7,sK5)
        | v2_struct_0(k1_tsep_1(sK5,sK7,X2))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X2),sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X2))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),k1_tsep_1(sK5,sK7,X2),sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f865,f179])).

fof(f865,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),X2,sK6)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),u1_struct_0(X2),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))))
        | sP1(sK6,X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),sK7,sK5)
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | v2_struct_0(k1_tsep_1(sK5,sK7,X2))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X2),sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X2))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),k1_tsep_1(sK5,sK7,X2),sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f864,f183])).

fof(f183,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f864,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),X2,sK6)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),u1_struct_0(X2),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))))
        | sP1(sK6,X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),sK7,sK5)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | v2_struct_0(k1_tsep_1(sK5,sK7,X2))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X2),sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X2))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),k1_tsep_1(sK5,sK7,X2),sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f863,f187])).

fof(f187,plain,
    ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f863,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),X2,sK6)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),u1_struct_0(X2),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))))
        | sP1(sK6,X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),sK7,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | v2_struct_0(k1_tsep_1(sK5,sK7,X2))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X2),sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X2))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),k1_tsep_1(sK5,sK7,X2),sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f853,f191])).

fof(f853,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
        | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),X2,sK6)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))),u1_struct_0(X2),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X2),X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2))))
        | sP1(sK6,X2,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),sK7,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | v2_struct_0(k1_tsep_1(sK5,sK7,X2))
        | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,X2),sK5)
        | ~ m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,X2))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,X2)),k1_tsep_1(sK5,sK7,X2),sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(superposition,[],[f130,f695])).

fof(f695,plain,
    ( ! [X0] :
        ( k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK5)
        | ~ m1_pre_topc(sK7,X0)
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f694,f155])).

fof(f694,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f691,f156])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)))
        | ~ sP4(sK6,sK7,k2_tmap_1(sK5,sK6,sK9,X0),X0,sK5) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(resolution,[],[f679,f157])).

fof(f679,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f678,f73])).

fof(f678,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f677,f74])).

fof(f677,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f676,f75])).

fof(f676,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f675,f76])).

fof(f675,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f674,f77])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f673,f78])).

fof(f673,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f672,f79])).

fof(f672,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f671,f80])).

fof(f671,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f670,f84])).

fof(f670,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f669,f85])).

fof(f669,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f667,f86])).

fof(f667,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK7,X0)
        | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
        | ~ v1_funct_1(sK9)
        | ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | k2_tmap_1(sK5,sK6,sK9,sK7) = k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))
        | ~ m1_subset_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0)),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k3_tmap_1(sK5,sK6,X0,sK7,k2_tmap_1(sK5,sK6,sK9,X0))) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(resolution,[],[f138,f420])).

fof(f420,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X1,k2_tmap_1(sK5,sK6,sK9,sK7))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(X1,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(X1) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f419,f179])).

fof(f419,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X1,k2_tmap_1(sK5,sK6,sK9,sK7))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X1
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(X1,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(X1) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f409,f183])).

fof(f409,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X1,k2_tmap_1(sK5,sK6,sK9,sK7))
        | k2_tmap_1(sK5,sK6,sK9,sK7) = X1
        | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        | ~ v1_funct_2(X1,u1_struct_0(sK7),u1_struct_0(sK6))
        | ~ v1_funct_1(X1) )
    | ~ spl10_8 ),
    inference(resolution,[],[f151,f191])).

fof(f130,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f436,plain,(
    spl10_18 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl10_18 ),
    inference(subsumption_resolution,[],[f434,f245])).

fof(f245,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f243,f75])).

fof(f243,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f121,f82])).

fof(f434,plain,
    ( ~ l1_pre_topc(sK8)
    | spl10_18 ),
    inference(resolution,[],[f383,f120])).

fof(f383,plain,
    ( ~ l1_struct_0(sK8)
    | spl10_18 ),
    inference(avatar_component_clause,[],[f381])).

fof(f407,plain,(
    spl10_16 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl10_16 ),
    inference(subsumption_resolution,[],[f405,f244])).

fof(f244,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f242,f75])).

fof(f242,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f121,f80])).

fof(f405,plain,
    ( ~ l1_pre_topc(sK7)
    | spl10_16 ),
    inference(resolution,[],[f373,f120])).

fof(f373,plain,
    ( ~ l1_struct_0(sK7)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f371])).

fof(f404,plain,(
    spl10_13 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl10_13 ),
    inference(subsumption_resolution,[],[f402,f75])).

fof(f402,plain,
    ( ~ l1_pre_topc(sK5)
    | spl10_13 ),
    inference(resolution,[],[f359,f120])).

fof(f359,plain,
    ( ~ l1_struct_0(sK5)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl10_13
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f401,plain,(
    spl10_14 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl10_14 ),
    inference(subsumption_resolution,[],[f399,f78])).

fof(f399,plain,
    ( ~ l1_pre_topc(sK6)
    | spl10_14 ),
    inference(resolution,[],[f363,f120])).

fof(f363,plain,
    ( ~ l1_struct_0(sK6)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl10_14
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f367,plain,
    ( ~ spl10_13
    | ~ spl10_14
    | spl10_15 ),
    inference(avatar_split_clause,[],[f355,f365,f361,f357])).

fof(f355,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP3(sK6,X0,sK9,sK5)
      | ~ l1_struct_0(sK6)
      | ~ l1_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f354,f84])).

fof(f354,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP3(sK6,X0,sK9,sK5)
      | ~ v1_funct_1(sK9)
      | ~ l1_struct_0(sK6)
      | ~ l1_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f345,f85])).

fof(f345,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP3(sK6,X0,sK9,sK5)
      | ~ v1_funct_2(sK9,u1_struct_0(sK5),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ l1_struct_0(sK6)
      | ~ l1_struct_0(sK5) ) ),
    inference(resolution,[],[f150,f86])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP3(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f47])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f231,plain,
    ( spl10_3
    | spl10_7 ),
    inference(avatar_split_clause,[],[f97,f186,f170])).

fof(f97,plain,
    ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f215,plain,
    ( spl10_3
    | spl10_11 ),
    inference(avatar_split_clause,[],[f113,f202,f170])).

fof(f113,plain,
    ( v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f209,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f119,f206,f202,f198,f194,f190,f186,f182,f178,f174,f170,f166,f162])).

fof(f119,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK8),sK8,sK6)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK8),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK8))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,sK7),sK7,sK6)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,sK7),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,sK7))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK6,sK9,k1_tsep_1(sK5,sK7,sK8))) ),
    inference(cnf_transformation,[],[f58])).

%------------------------------------------------------------------------------

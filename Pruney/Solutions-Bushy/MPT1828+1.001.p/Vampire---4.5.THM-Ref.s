%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1828+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:40 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  259 (3275 expanded)
%              Number of leaves         :   27 (1635 expanded)
%              Depth                    :   54
%              Number of atoms          : 2052 (79137 expanded)
%              Number of equality atoms :   47 ( 132 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f228,f359,f547,f556,f645,f668,f676,f747,f768])).

fof(f768,plain,(
    spl12_6 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl12_6 ),
    inference(subsumption_resolution,[],[f766,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
      | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
      | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
      | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) )
    & r4_tsep_1(sK6,sK8,sK9)
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),sK11))
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    & v5_pre_topc(sK11,sK9,sK7)
    & v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
    & v5_pre_topc(sK10,sK8,sK7)
    & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    & v1_funct_1(sK10)
    & ~ r1_tsep_1(sK8,sK9)
    & m1_pre_topc(sK9,sK6)
    & ~ v2_struct_0(sK9)
    & m1_pre_topc(sK8,sK6)
    & ~ v2_struct_0(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f11,f39,f38,f37,f36,f35,f34])).

fof(f34,plain,
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
                    & ~ r1_tsep_1(X2,X3)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK6,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK6,X1,X2,X3,X4,X5),k1_tsep_1(sK6,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK6,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK6,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK6,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK6,X1,X2,k2_tsep_1(sK6,X2,X3),X4),k3_tmap_1(sK6,X1,X3,k2_tsep_1(sK6,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,sK6)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK6)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK6,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK6,X1,X2,X3,X4,X5),k1_tsep_1(sK6,X2,X3),X1)
                          | ~ v1_funct_2(k10_tmap_1(sK6,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK6,X1,X2,X3,X4,X5)) )
                        & r4_tsep_1(sK6,X2,X3)
                        & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK6,X1,X2,k2_tsep_1(sK6,X2,X3),X4),k3_tmap_1(sK6,X1,X3,k2_tsep_1(sK6,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,sK6)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK6)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(sK7))))
                        | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,X2,X3,X4,X5),k1_tsep_1(sK6,X2,X3),sK7)
                        | ~ v1_funct_2(k10_tmap_1(sK6,sK7,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(sK7))
                        | ~ v1_funct_1(k10_tmap_1(sK6,sK7,X2,X3,X4,X5)) )
                      & r4_tsep_1(sK6,X2,X3)
                      & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,X2,X3)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,X2,k2_tsep_1(sK6,X2,X3),X4),k3_tmap_1(sK6,sK7,X3,k2_tsep_1(sK6,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
                      & v5_pre_topc(X5,X3,sK7)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK7))))
                  & v5_pre_topc(X4,X2,sK7)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK7))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,sK6)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK6)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(sK7))))
                      | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,X2,X3,X4,X5),k1_tsep_1(sK6,X2,X3),sK7)
                      | ~ v1_funct_2(k10_tmap_1(sK6,sK7,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(sK7))
                      | ~ v1_funct_1(k10_tmap_1(sK6,sK7,X2,X3,X4,X5)) )
                    & r4_tsep_1(sK6,X2,X3)
                    & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,X2,X3)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,X2,k2_tsep_1(sK6,X2,X3),X4),k3_tmap_1(sK6,sK7,X3,k2_tsep_1(sK6,X2,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
                    & v5_pre_topc(X5,X3,sK7)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK7))))
                & v5_pre_topc(X4,X2,sK7)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK7))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(X2,X3)
            & m1_pre_topc(X3,sK6)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK6)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7))))
                    | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),k1_tsep_1(sK6,sK8,X3),sK7)
                    | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7))
                    | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5)) )
                  & r4_tsep_1(sK6,sK8,X3)
                  & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,X3),X4),k3_tmap_1(sK6,sK7,X3,k2_tsep_1(sK6,sK8,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
                  & v5_pre_topc(X5,X3,sK7)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
              & v5_pre_topc(X4,sK8,sK7)
              & v1_funct_2(X4,u1_struct_0(sK8),u1_struct_0(sK7))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(sK8,X3)
          & m1_pre_topc(X3,sK6)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK8,sK6)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7))))
                  | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),k1_tsep_1(sK6,sK8,X3),sK7)
                  | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7))
                  | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5)) )
                & r4_tsep_1(sK6,sK8,X3)
                & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,X3),X4),k3_tmap_1(sK6,sK7,X3,k2_tsep_1(sK6,sK8,X3),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
                & v5_pre_topc(X5,X3,sK7)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
            & v5_pre_topc(X4,sK8,sK7)
            & v1_funct_2(X4,u1_struct_0(sK8),u1_struct_0(sK7))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(sK8,X3)
        & m1_pre_topc(X3,sK6)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
                | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_tsep_1(sK6,sK8,sK9),sK7)
                | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
                | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5)) )
              & r4_tsep_1(sK6,sK8,sK9)
              & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),X4),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
              & v5_pre_topc(X5,sK9,sK7)
              & v1_funct_2(X5,u1_struct_0(sK9),u1_struct_0(sK7))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
          & v5_pre_topc(X4,sK8,sK7)
          & v1_funct_2(X4,u1_struct_0(sK8),u1_struct_0(sK7))
          & v1_funct_1(X4) )
      & ~ r1_tsep_1(sK8,sK9)
      & m1_pre_topc(sK9,sK6)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
              | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_tsep_1(sK6,sK8,sK9),sK7)
              | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
              | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5)) )
            & r4_tsep_1(sK6,sK8,sK9)
            & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),X4),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
            & v5_pre_topc(X5,sK9,sK7)
            & v1_funct_2(X5,u1_struct_0(sK9),u1_struct_0(sK7))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
        & v5_pre_topc(X4,sK8,sK7)
        & v1_funct_2(X4,u1_struct_0(sK8),u1_struct_0(sK7))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
            | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5),k1_tsep_1(sK6,sK8,sK9),sK7)
            | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
            | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5)) )
          & r4_tsep_1(sK6,sK8,sK9)
          & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
          & v5_pre_topc(X5,sK9,sK7)
          & v1_funct_2(X5,u1_struct_0(sK9),u1_struct_0(sK7))
          & v1_funct_1(X5) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      & v5_pre_topc(sK10,sK8,sK7)
      & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
          | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5),k1_tsep_1(sK6,sK8,sK9),sK7)
          | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
          | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,X5)) )
        & r4_tsep_1(sK6,sK8,sK9)
        & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
        & v5_pre_topc(X5,sK9,sK7)
        & v1_funct_2(X5,u1_struct_0(sK9),u1_struct_0(sK7))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
        | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
        | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
        | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) )
      & r4_tsep_1(sK6,sK8,sK9)
      & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),sK11))
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      & v5_pre_topc(sK11,sK9,sK7)
      & v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
                  & ~ r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
                  & ~ r1_tsep_1(X2,X3)
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

fof(f766,plain,
    ( v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f765,f59])).

fof(f59,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f765,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f764,f60])).

fof(f60,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f764,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f763,f65])).

fof(f65,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f763,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f762,f67])).

fof(f67,plain,(
    m1_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f762,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(resolution,[],[f761,f519])).

fof(f519,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f518,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f518,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f517,f69])).

fof(f69,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f40])).

fof(f517,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ v1_funct_1(sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f509,f70])).

fof(f70,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f509,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f429,f72])).

fof(f72,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f429,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f428,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f428,plain,(
    ! [X4,X5,X3] :
      ( sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f427,f62])).

fof(f62,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f427,plain,(
    ! [X4,X5,X3] :
      ( sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f426,f63])).

fof(f63,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f426,plain,(
    ! [X4,X5,X3] :
      ( sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f425,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f40])).

fof(f425,plain,(
    ! [X4,X5,X3] :
      ( sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | v2_struct_0(sK9)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f424,f73])).

fof(f73,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f40])).

fof(f424,plain,(
    ! [X4,X5,X3] :
      ( sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | v2_struct_0(sK9)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f412,f74])).

fof(f74,plain,(
    v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f412,plain,(
    ! [X4,X5,X3] :
      ( sP5(sK7,sK9,X3,X4,sK11,X5)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK9,X4)
      | v2_struct_0(sK9)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f113,f76])).

fof(f76,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP5(X1,X3,X2,X0,X5,X4)
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP5(X1,X3,X2,X0,X5,X4)
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
    inference(definition_folding,[],[f23,f32])).

fof(f32,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP5(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f761,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_6 ),
    inference(resolution,[],[f358,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP5(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP5(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP5(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f358,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
    | spl12_6 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl12_6
  <=> m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f747,plain,
    ( ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f745,f58])).

fof(f745,plain,
    ( v2_struct_0(sK6)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f744,f59])).

fof(f744,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f743,f60])).

fof(f743,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f742,f65])).

fof(f742,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f741,f67])).

fof(f741,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(resolution,[],[f740,f519])).

fof(f740,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f739,f58])).

fof(f739,plain,
    ( v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f738,f59])).

fof(f738,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f737,f60])).

fof(f737,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f736,f61])).

fof(f736,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f735,f62])).

fof(f735,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f734,f63])).

fof(f734,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f733,f64])).

fof(f733,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f732,f65])).

fof(f732,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f731,f66])).

fof(f731,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f730,f67])).

fof(f730,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f729,f78])).

fof(f78,plain,(
    r4_tsep_1(sK6,sK8,sK9) ),
    inference(cnf_transformation,[],[f40])).

fof(f729,plain,
    ( ~ r4_tsep_1(sK6,sK8,sK9)
    | ~ m1_pre_topc(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | spl12_5
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f728,f557])).

fof(f557,plain,
    ( ~ sP2(sK7,sK9,sK8,sK6,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | spl12_5 ),
    inference(resolution,[],[f354,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP2(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        | ~ v1_funct_1(X4) )
      & ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(X4) )
        | ~ sP2(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( ( sP2(X1,X3,X2,X0,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        | ~ v1_funct_1(X4) )
      & ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
        | ~ sP2(X1,X3,X2,X0,X4) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( ( sP2(X1,X3,X2,X0,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        | ~ v1_funct_1(X4) )
      & ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
        | ~ sP2(X1,X3,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP2(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f354,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl12_5
  <=> v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f728,plain,
    ( sP2(sK7,sK9,sK8,sK6,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ r4_tsep_1(sK6,sK8,sK9)
    | ~ m1_pre_topc(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(resolution,[],[f725,f410])).

fof(f410,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP3(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP2(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ r4_tsep_1(X28,X29,X27)
      | ~ m1_pre_topc(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP5(X26,X27,X29,X28,X31,X30) ) ),
    inference(subsumption_resolution,[],[f409,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP5(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f409,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP3(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP2(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ v1_funct_1(k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ r4_tsep_1(X28,X29,X27)
      | ~ m1_pre_topc(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP5(X26,X27,X29,X28,X31,X30) ) ),
    inference(subsumption_resolution,[],[f406,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP5(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f406,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP3(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP2(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ v1_funct_2(k10_tmap_1(X28,X26,X29,X27,X30,X31),u1_struct_0(k1_tsep_1(X28,X29,X27)),u1_struct_0(X26))
      | ~ v1_funct_1(k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ r4_tsep_1(X28,X29,X27)
      | ~ m1_pre_topc(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP5(X26,X27,X29,X28,X31,X30) ) ),
    inference(resolution,[],[f101,f112])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ sP3(X1,X3,X4,X2,X0)
      | sP2(X1,X3,X2,X0,X4)
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
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( sP2(X1,X3,X2,X0,X4)
                          | ~ sP3(X1,X3,X4,X2,X0) )
                        & ( sP3(X1,X3,X4,X2,X0)
                          | ~ sP2(X1,X3,X2,X0,X4) ) )
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( sP2(X1,X3,X2,X0,X4)
                      <=> sP3(X1,X3,X4,X2,X0) )
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
    inference(definition_folding,[],[f15,f28,f27])).

fof(f28,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP3(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f725,plain,
    ( sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f724,f74])).

fof(f724,plain,
    ( ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(forward_demodulation,[],[f723,f717])).

fof(f717,plain,
    ( sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_2
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f716,f67])).

fof(f716,plain,
    ( sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f715,f666])).

fof(f666,plain,
    ( m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl12_14
  <=> m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f715,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f714,f58])).

fof(f714,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f713,f59])).

fof(f713,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f712,f60])).

fof(f712,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f711,f65])).

fof(f711,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(resolution,[],[f541,f227])).

fof(f227,plain,
    ( sP0(sK11,sK10,sK9,sK8,sK7,sK6)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl12_2
  <=> sP0(sK11,sK10,sK9,sK8,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f541,plain,(
    ! [X0] :
      ( ~ sP0(sK11,sK10,sK9,sK8,sK7,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,sK9),X0)
      | sK11 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,sK9),sK9,k10_tmap_1(X0,sK7,sK8,sK9,sK10,sK11))
      | ~ m1_pre_topc(sK9,X0) ) ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,sK9),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK9,X0)
      | sK11 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,sK9),sK9,k10_tmap_1(X0,sK7,sK8,sK9,sK10,sK11))
      | ~ sP0(sK11,sK10,sK9,sK8,sK7,X0) ) ),
    inference(resolution,[],[f519,f334])).

fof(f334,plain,(
    ! [X10,X11,X9] :
      ( ~ sP5(sK7,sK9,X10,X9,sK11,X11)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,sK9),X9)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(sK9,X9)
      | sK11 = k3_tmap_1(X9,sK7,k1_tsep_1(X9,X10,sK9),sK9,k10_tmap_1(X9,sK7,X10,sK9,X11,sK11))
      | ~ sP0(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(subsumption_resolution,[],[f333,f61])).

fof(f333,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_pre_topc(sK9,X9)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,sK9),X9)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP5(sK7,sK9,X10,X9,sK11,X11)
      | sK11 = k3_tmap_1(X9,sK7,k1_tsep_1(X9,X10,sK9),sK9,k10_tmap_1(X9,sK7,X10,sK9,X11,sK11))
      | ~ sP0(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(subsumption_resolution,[],[f332,f62])).

fof(f332,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_pre_topc(sK9,X9)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,sK9),X9)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP5(sK7,sK9,X10,X9,sK11,X11)
      | sK11 = k3_tmap_1(X9,sK7,k1_tsep_1(X9,X10,sK9),sK9,k10_tmap_1(X9,sK7,X10,sK9,X11,sK11))
      | ~ sP0(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(subsumption_resolution,[],[f321,f63])).

fof(f321,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_pre_topc(sK9,X9)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,sK9),X9)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP5(sK7,sK9,X10,X9,sK11,X11)
      | sK11 = k3_tmap_1(X9,sK7,k1_tsep_1(X9,X10,sK9),sK9,k10_tmap_1(X9,sK7,X10,sK9,X11,sK11))
      | ~ sP0(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(resolution,[],[f255,f184])).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( ~ sP4(sK7,sK9,k10_tmap_1(X3,sK7,X4,sK9,X5,sK11),k1_tsep_1(X3,X4,sK9),X3)
      | sK11 = k3_tmap_1(X3,sK7,k1_tsep_1(X3,X4,sK9),sK9,k10_tmap_1(X3,sK7,X4,sK9,X5,sK11))
      | ~ sP0(sK11,X5,sK9,X4,sK7,X3) ) ),
    inference(resolution,[],[f176,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1) )
      & ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X5,X4,X3,X2,X1,X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
      & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
        | ~ sP0(X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X5,X4,X3,X2,X1,X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
      & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
        | ~ sP0(X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( sP0(X5,X4,X3,X2,X1,X0)
    <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK9,X2),sK11)
      | sK11 = k3_tmap_1(X0,sK7,X1,sK9,X2)
      | ~ sP4(sK7,sK9,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f175,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP4(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP4(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK7,X1,sK9,X2)
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK9,X2),sK11)
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK9,X2))
      | ~ sP4(sK7,sK9,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f172,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK7,X1,sK9,X2)
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK9,X2),sK11)
      | ~ v1_funct_2(k3_tmap_1(X0,sK7,X1,sK9,X2),u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK9,X2))
      | ~ sP4(sK7,sK9,X2,X1,X0) ) ),
    inference(resolution,[],[f150,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f150,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | sK11 = X1
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),X1,sK11)
      | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f149,f73])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),X1,sK11)
      | sK11 = X1
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f141,f74])).

fof(f141,plain,(
    ! [X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),X1,sK11)
      | sK11 = X1
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f104,f76])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f255,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34,X32] :
      ( sP4(X32,X33,k10_tmap_1(X34,X32,X35,X36,X37,X38),k1_tsep_1(X34,X35,X36),X39)
      | ~ m1_pre_topc(X33,X39)
      | ~ m1_pre_topc(k1_tsep_1(X34,X35,X36),X39)
      | ~ l1_pre_topc(X32)
      | ~ v2_pre_topc(X32)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(X39)
      | ~ v2_pre_topc(X39)
      | v2_struct_0(X39)
      | ~ sP5(X32,X36,X35,X34,X38,X37) ) ),
    inference(subsumption_resolution,[],[f254,f110])).

fof(f254,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34,X32] :
      ( sP4(X32,X33,k10_tmap_1(X34,X32,X35,X36,X37,X38),k1_tsep_1(X34,X35,X36),X39)
      | ~ v1_funct_1(k10_tmap_1(X34,X32,X35,X36,X37,X38))
      | ~ m1_pre_topc(X33,X39)
      | ~ m1_pre_topc(k1_tsep_1(X34,X35,X36),X39)
      | ~ l1_pre_topc(X32)
      | ~ v2_pre_topc(X32)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(X39)
      | ~ v2_pre_topc(X39)
      | v2_struct_0(X39)
      | ~ sP5(X32,X36,X35,X34,X38,X37) ) ),
    inference(subsumption_resolution,[],[f235,f111])).

fof(f235,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34,X32] :
      ( sP4(X32,X33,k10_tmap_1(X34,X32,X35,X36,X37,X38),k1_tsep_1(X34,X35,X36),X39)
      | ~ v1_funct_2(k10_tmap_1(X34,X32,X35,X36,X37,X38),u1_struct_0(k1_tsep_1(X34,X35,X36)),u1_struct_0(X32))
      | ~ v1_funct_1(k10_tmap_1(X34,X32,X35,X36,X37,X38))
      | ~ m1_pre_topc(X33,X39)
      | ~ m1_pre_topc(k1_tsep_1(X34,X35,X36),X39)
      | ~ l1_pre_topc(X32)
      | ~ v2_pre_topc(X32)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(X39)
      | ~ v2_pre_topc(X39)
      | v2_struct_0(X39)
      | ~ sP5(X32,X36,X35,X34,X38,X37) ) ),
    inference(resolution,[],[f109,f112])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(definition_folding,[],[f21,f30])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f723,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f722,f75])).

fof(f75,plain,(
    v5_pre_topc(sK11,sK9,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f722,plain,
    ( ~ v5_pre_topc(sK11,sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(forward_demodulation,[],[f721,f717])).

fof(f721,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f720,f76])).

fof(f720,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(forward_demodulation,[],[f719,f717])).

fof(f719,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f718,f73])).

fof(f718,plain,
    ( ~ v1_funct_1(sK11)
    | ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_2
    | ~ spl12_13
    | ~ spl12_14 ),
    inference(backward_demodulation,[],[f710,f717])).

fof(f710,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f709,f69])).

fof(f709,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v1_funct_1(sK10)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f708,f70])).

fof(f708,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ v1_funct_1(sK10)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f707,f71])).

fof(f71,plain,(
    v5_pre_topc(sK10,sK8,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f707,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v5_pre_topc(sK10,sK8,sK7)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ v1_funct_1(sK10)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f693,f72])).

fof(f693,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP3(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v5_pre_topc(sK10,sK8,sK7)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ v1_funct_1(sK10)
    | ~ spl12_13 ),
    inference(superposition,[],[f94,f663])).

fof(f663,plain,
    ( sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl12_13
  <=> sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | sP3(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP3(X0,X1,X2,X3,X4)
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
        | ~ sP3(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP3(X1,X3,X4,X2,X0)
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
        | ~ sP3(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP3(X1,X3,X4,X2,X0)
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
        | ~ sP3(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f676,plain,(
    spl12_14 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | spl12_14 ),
    inference(subsumption_resolution,[],[f674,f58])).

fof(f674,plain,
    ( v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f673,f60])).

fof(f673,plain,
    ( ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f672,f64])).

fof(f672,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f671,f65])).

fof(f671,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f670,f66])).

fof(f670,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f669,f67])).

fof(f669,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(resolution,[],[f667,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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

fof(f667,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | spl12_14 ),
    inference(avatar_component_clause,[],[f665])).

fof(f668,plain,
    ( spl12_13
    | ~ spl12_14
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f659,f225,f665,f661])).

fof(f659,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f658,f67])).

fof(f658,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f657,f58])).

fof(f657,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f656,f59])).

fof(f656,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f655,f60])).

fof(f655,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f654,f65])).

fof(f654,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(resolution,[],[f540,f227])).

fof(f540,plain,(
    ! [X1] :
      ( ~ sP0(sK11,sK10,sK9,sK8,sK7,X1)
      | ~ m1_pre_topc(sK8,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK8,sK9),X1)
      | sK10 = k3_tmap_1(X1,sK7,k1_tsep_1(X1,sK8,sK9),sK8,k10_tmap_1(X1,sK7,sK8,sK9,sK10,sK11))
      | ~ m1_pre_topc(sK9,X1) ) ),
    inference(duplicate_literal_removal,[],[f538])).

fof(f538,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK9,X1)
      | ~ m1_pre_topc(sK8,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK8,sK9),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK8,X1)
      | sK10 = k3_tmap_1(X1,sK7,k1_tsep_1(X1,sK8,sK9),sK8,k10_tmap_1(X1,sK7,sK8,sK9,sK10,sK11))
      | ~ sP0(sK11,sK10,sK9,sK8,sK7,X1) ) ),
    inference(resolution,[],[f519,f325])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(sK7,X1,sK8,X0,X2,sK10)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK8,X0)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP0(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f324,f61])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,X1),X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP5(sK7,X1,sK8,X0,X2,sK10)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP0(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f323,f62])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,X1),X0)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP5(sK7,X1,sK8,X0,X2,sK10)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP0(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f318,f63])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,X1),X0)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP5(sK7,X1,sK8,X0,X2,sK10)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP0(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(resolution,[],[f255,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(sK7,sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2),k1_tsep_1(X0,sK8,X1),X0)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP0(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(resolution,[],[f166,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1)
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK8,X2),sK10)
      | sK10 = k3_tmap_1(X0,sK7,X1,sK8,X2)
      | ~ sP4(sK7,sK8,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f165,f106])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( sK10 = k3_tmap_1(X0,sK7,X1,sK8,X2)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK8,X2),sK10)
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK8,X2))
      | ~ sP4(sK7,sK8,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f162,f107])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( sK10 = k3_tmap_1(X0,sK7,X1,sK8,X2)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK8,X2),sK10)
      | ~ v1_funct_2(k3_tmap_1(X0,sK7,X1,sK8,X2),u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK8,X2))
      | ~ sP4(sK7,sK8,X2,X1,X0) ) ),
    inference(resolution,[],[f148,f108])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      | sK10 = X0
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),X0,sK10)
      | ~ v1_funct_2(X0,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f147,f69])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),X0,sK10)
      | sK10 = X0
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      | ~ v1_funct_2(X0,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f140,f70])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),X0,sK10)
      | sK10 = X0
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      | ~ v1_funct_2(X0,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f104,f72])).

fof(f645,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f643,f58])).

fof(f643,plain,
    ( v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f642,f59])).

fof(f642,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f641,f60])).

fof(f641,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f640,f65])).

fof(f640,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f639,f67])).

fof(f639,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(resolution,[],[f625,f223])).

fof(f223,plain,
    ( ~ sP1(sK11,sK9,sK8,sK6,sK7,sK10)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl12_1
  <=> sP1(sK11,sK9,sK8,sK6,sK7,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f625,plain,(
    ! [X0] :
      ( sP1(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f624,f64])).

fof(f624,plain,(
    ! [X0] :
      ( sP1(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f623,f68])).

fof(f68,plain,(
    ~ r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f40])).

fof(f623,plain,(
    ! [X0] :
      ( sP1(sK11,sK9,sK8,X0,sK7,sK10)
      | r1_tsep_1(sK8,sK9)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f622,f69])).

fof(f622,plain,(
    ! [X0] :
      ( sP1(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ v1_funct_1(sK10)
      | r1_tsep_1(sK8,sK9)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f614,f70])).

fof(f614,plain,(
    ! [X0] :
      ( sP1(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(sK10)
      | r1_tsep_1(sK8,sK9)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f496,f72])).

fof(f496,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f495,f61])).

fof(f495,plain,(
    ! [X4,X5,X3] :
      ( sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f494,f62])).

fof(f494,plain,(
    ! [X4,X5,X3] :
      ( sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f493,f63])).

fof(f493,plain,(
    ! [X4,X5,X3] :
      ( sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f492,f66])).

fof(f492,plain,(
    ! [X4,X5,X3] :
      ( sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | v2_struct_0(sK9)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f491,f73])).

fof(f491,plain,(
    ! [X4,X5,X3] :
      ( sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | v2_struct_0(sK9)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f479,f74])).

fof(f479,plain,(
    ! [X4,X5,X3] :
      ( sP1(sK11,sK9,X3,X4,sK7,X5)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | v2_struct_0(sK9)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f85,f76])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP1(X5,X3,X2,X0,X1,X4)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( sP1(X5,X3,X2,X0,X1,X4)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
    inference(definition_folding,[],[f13,f25,f24])).

fof(f25,plain,(
    ! [X5,X3,X2,X0,X1,X4] :
      ( ( sP0(X5,X4,X3,X2,X1,X0)
      <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
      | ~ sP1(X5,X3,X2,X0,X1,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).

fof(f556,plain,(
    spl12_4 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl12_4 ),
    inference(subsumption_resolution,[],[f554,f58])).

fof(f554,plain,
    ( v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f553,f59])).

fof(f553,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f552,f60])).

fof(f552,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f551,f65])).

fof(f551,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f550,f67])).

fof(f550,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(resolution,[],[f549,f519])).

fof(f549,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_4 ),
    inference(resolution,[],[f350,f111])).

fof(f350,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl12_4
  <=> v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f547,plain,(
    spl12_3 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl12_3 ),
    inference(subsumption_resolution,[],[f545,f58])).

fof(f545,plain,
    ( v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f544,f59])).

fof(f544,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f543,f60])).

fof(f543,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f542,f65])).

fof(f542,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f539,f67])).

fof(f539,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(resolution,[],[f519,f360])).

fof(f360,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_3 ),
    inference(resolution,[],[f346,f110])).

fof(f346,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl12_3
  <=> v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f359,plain,
    ( ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f79,f356,f352,f348,f344])).

fof(f79,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
    | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f40])).

fof(f228,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f216,f225,f221])).

fof(f216,plain,
    ( sP0(sK11,sK10,sK9,sK8,sK7,sK6)
    | ~ sP1(sK11,sK9,sK8,sK6,sK7,sK10) ),
    inference(resolution,[],[f81,f77])).

fof(f77,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),sK11)) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0))
      | sP0(X0,X5,X1,X2,X4,X3)
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( sP0(X0,X5,X1,X2,X4,X3)
          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0)) )
        & ( r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0))
          | ~ sP0(X0,X5,X1,X2,X4,X3) ) )
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X5,X3,X2,X0,X1,X4] :
      ( ( ( sP0(X5,X4,X3,X2,X1,X0)
          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
        & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          | ~ sP0(X5,X4,X3,X2,X1,X0) ) )
      | ~ sP1(X5,X3,X2,X0,X1,X4) ) ),
    inference(nnf_transformation,[],[f25])).

%------------------------------------------------------------------------------

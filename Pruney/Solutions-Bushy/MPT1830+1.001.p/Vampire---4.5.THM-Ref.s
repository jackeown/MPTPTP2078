%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:40 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  262 (2253 expanded)
%              Number of leaves         :   28 (1144 expanded)
%              Depth                    :   39
%              Number of atoms          : 2059 (56311 expanded)
%              Number of equality atoms :   48 (  62 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f878,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f227,f360,f519,f528,f660,f689,f697,f730,f855,f877])).

fof(f877,plain,(
    spl12_6 ),
    inference(avatar_contradiction_clause,[],[f876])).

fof(f876,plain,
    ( $false
    | spl12_6 ),
    inference(subsumption_resolution,[],[f875,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
      | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
      | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
      | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) )
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
    & v1_borsuk_1(sK9,sK6)
    & ~ v2_struct_0(sK9)
    & m1_pre_topc(sK8,sK6)
    & v1_borsuk_1(sK8,sK6)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK6,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK6,X1,X2,X3,X4,X5),k1_tsep_1(sK6,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK6,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK6,X1,X2,X3,X4,X5)) )
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
                  & v1_borsuk_1(X3,sK6)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK6)
              & v1_borsuk_1(X2,sK6)
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
                & v1_borsuk_1(X3,sK6)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK6)
            & v1_borsuk_1(X2,sK6)
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
              & v1_borsuk_1(X3,sK6)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK6)
          & v1_borsuk_1(X2,sK6)
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
            & v1_borsuk_1(X3,sK6)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK6)
        & v1_borsuk_1(X2,sK6)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7))))
                    | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),k1_tsep_1(sK6,sK8,X3),sK7)
                    | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,X3)),u1_struct_0(sK7))
                    | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,X3,X4,X5)) )
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
          & v1_borsuk_1(X3,sK6)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK8,sK6)
      & v1_borsuk_1(sK8,sK6)
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
        & v1_borsuk_1(X3,sK6)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
                | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_tsep_1(sK6,sK8,sK9),sK7)
                | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
                | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5)) )
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
      & v1_borsuk_1(sK9,sK6)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
              | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),k1_tsep_1(sK6,sK8,sK9),sK7)
              | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
              | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,X4,X5)) )
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
        & r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
        & v5_pre_topc(X5,sK9,sK7)
        & v1_funct_2(X5,u1_struct_0(sK9),u1_struct_0(sK7))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
        | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
        | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
        | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) )
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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
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
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
                           => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_tmap_1)).

fof(f875,plain,
    ( v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f874,f59])).

fof(f59,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f874,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f873,f60])).

fof(f60,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f873,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f872,f66])).

fof(f66,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f872,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f871,f69])).

fof(f69,plain,(
    m1_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f871,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_6 ),
    inference(resolution,[],[f870,f491])).

fof(f491,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f490,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f490,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f489,f71])).

fof(f71,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f40])).

fof(f489,plain,(
    ! [X0] :
      ( sP5(sK7,sK9,sK8,X0,sK11,sK10)
      | ~ v1_funct_1(sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f481,f72])).

fof(f72,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f481,plain,(
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
    inference(resolution,[],[f421,f74])).

fof(f74,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f421,plain,(
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
    inference(subsumption_resolution,[],[f420,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f420,plain,(
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
    inference(subsumption_resolution,[],[f419,f62])).

fof(f62,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f419,plain,(
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
    inference(subsumption_resolution,[],[f418,f63])).

fof(f63,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f418,plain,(
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
    inference(subsumption_resolution,[],[f417,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f40])).

fof(f417,plain,(
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
    inference(subsumption_resolution,[],[f416,f75])).

fof(f75,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f40])).

fof(f416,plain,(
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
    inference(subsumption_resolution,[],[f404,f76])).

fof(f76,plain,(
    v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f404,plain,(
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
    inference(resolution,[],[f114,f78])).

fof(f78,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f870,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_6 ),
    inference(resolution,[],[f359,f113])).

fof(f113,plain,(
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

fof(f359,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
    | spl12_6 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl12_6
  <=> m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f855,plain,
    ( spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f853,f58])).

fof(f853,plain,
    ( v2_struct_0(sK6)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f852,f59])).

fof(f852,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f851,f60])).

fof(f851,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f850,f66])).

fof(f850,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f849,f69])).

fof(f849,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(resolution,[],[f848,f491])).

fof(f848,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f847,f58])).

fof(f847,plain,
    ( v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f846,f59])).

fof(f846,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f845,f60])).

fof(f845,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f844,f61])).

fof(f844,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f843,f62])).

fof(f843,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f842,f63])).

fof(f842,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f841,f64])).

fof(f841,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f840,f65])).

fof(f65,plain,(
    v1_borsuk_1(sK8,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f840,plain,
    ( ~ v1_borsuk_1(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f839,f66])).

fof(f839,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ v1_borsuk_1(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f838,f67])).

fof(f838,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ v1_borsuk_1(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f837,f68])).

fof(f68,plain,(
    v1_borsuk_1(sK9,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f837,plain,
    ( ~ v1_borsuk_1(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ v1_borsuk_1(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f836,f69])).

fof(f836,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ v1_borsuk_1(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ v1_borsuk_1(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_5
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f835,f529])).

fof(f529,plain,
    ( ~ sP0(sK7,sK9,sK8,sK6,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | spl12_5 ),
    inference(resolution,[],[f355,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f355,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl12_5
  <=> v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f835,plain,
    ( sP0(sK7,sK9,sK8,sK6,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ v1_borsuk_1(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ v1_borsuk_1(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(resolution,[],[f480,f788])).

fof(f788,plain,
    ( sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f787,f75])).

fof(f787,plain,
    ( ~ v1_funct_1(sK11)
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(forward_demodulation,[],[f786,f684])).

fof(f684,plain,
    ( sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl12_13
  <=> sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f786,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f785,f76])).

fof(f785,plain,
    ( ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(forward_demodulation,[],[f784,f684])).

fof(f784,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f783,f77])).

fof(f77,plain,(
    v5_pre_topc(sK11,sK9,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f783,plain,
    ( ~ v5_pre_topc(sK11,sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(forward_demodulation,[],[f782,f684])).

fof(f782,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f781,f78])).

fof(f781,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_13
    | ~ spl12_15 ),
    inference(forward_demodulation,[],[f780,f684])).

fof(f780,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f779,f71])).

fof(f779,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v1_funct_1(sK10)
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f778,f72])).

fof(f778,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ v1_funct_1(sK10)
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f777,f73])).

fof(f73,plain,(
    v5_pre_topc(sK10,sK8,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f777,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v5_pre_topc(sK10,sK8,sK7)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ v1_funct_1(sK10)
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f772,f74])).

fof(f772,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),sK9,sK7)
    | ~ v1_funct_2(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)))
    | sP1(sK7,sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),sK8,sK6)
    | ~ v5_pre_topc(sK10,sK8,sK7)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ v1_funct_1(sK10)
    | ~ spl12_15 ),
    inference(superposition,[],[f89,f729])).

fof(f729,plain,
    ( sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl12_15
  <=> sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f480,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP1(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP0(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ m1_pre_topc(X27,X28)
      | ~ v1_borsuk_1(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_borsuk_1(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP5(X26,X27,X29,X28,X31,X30) ) ),
    inference(subsumption_resolution,[],[f479,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP5(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f479,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP1(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP0(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ v1_funct_1(k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ m1_pre_topc(X27,X28)
      | ~ v1_borsuk_1(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_borsuk_1(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP5(X26,X27,X29,X28,X31,X30) ) ),
    inference(subsumption_resolution,[],[f476,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP5(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f476,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP1(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP0(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ v1_funct_2(k10_tmap_1(X28,X26,X29,X27,X30,X31),u1_struct_0(k1_tsep_1(X28,X29,X27)),u1_struct_0(X26))
      | ~ v1_funct_1(k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ m1_pre_topc(X27,X28)
      | ~ v1_borsuk_1(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_borsuk_1(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP5(X26,X27,X29,X28,X31,X30) ) ),
    inference(resolution,[],[f96,f113])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(definition_folding,[],[f13,f25,f24])).

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

fof(f730,plain,
    ( spl12_15
    | ~ spl12_14
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f672,f224,f686,f727])).

fof(f686,plain,
    ( spl12_14
  <=> m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f224,plain,
    ( spl12_2
  <=> sP2(sK11,sK10,sK9,sK8,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f672,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f671,f69])).

fof(f671,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f670,f58])).

fof(f670,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f669,f59])).

fof(f669,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f668,f60])).

fof(f668,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f662,f66])).

fof(f662,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK10 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK8,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(resolution,[],[f226,f512])).

fof(f512,plain,(
    ! [X1] :
      ( ~ sP2(sK11,sK10,sK9,sK8,sK7,X1)
      | ~ m1_pre_topc(sK8,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK8,sK9),X1)
      | sK10 = k3_tmap_1(X1,sK7,k1_tsep_1(X1,sK8,sK9),sK8,k10_tmap_1(X1,sK7,sK8,sK9,sK10,sK11))
      | ~ m1_pre_topc(sK9,X1) ) ),
    inference(duplicate_literal_removal,[],[f510])).

fof(f510,plain,(
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
      | ~ sP2(sK11,sK10,sK9,sK8,sK7,X1) ) ),
    inference(resolution,[],[f491,f326])).

fof(f326,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(sK7,X1,sK8,X0,X2,sK10)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK8,X0)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP2(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f325,f61])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,X1),X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP5(sK7,X1,sK8,X0,X2,sK10)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP2(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f324,f62])).

fof(f324,plain,(
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
      | ~ sP2(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f319,f63])).

fof(f319,plain,(
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
      | ~ sP2(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(resolution,[],[f254,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(sK7,sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2),k1_tsep_1(X0,sK8,X1),X0)
      | sK10 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,X1),sK8,k10_tmap_1(X0,sK7,sK8,X1,sK10,X2))
      | ~ sP2(X2,sK10,X1,sK8,sK7,X0) ) ),
    inference(resolution,[],[f167,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP2(X0,X1,X2,X3,X4,X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1) )
      & ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1) )
        | ~ sP2(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X5,X4,X3,X2,X1,X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
      & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
        | ~ sP2(X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X5,X4,X3,X2,X1,X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
      & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
        | ~ sP2(X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( sP2(X5,X4,X3,X2,X1,X0)
    <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK8,X2),sK10)
      | sK10 = k3_tmap_1(X0,sK7,X1,sK8,X2)
      | ~ sP4(sK7,sK8,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f166,f107])).

fof(f107,plain,(
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

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( sK10 = k3_tmap_1(X0,sK7,X1,sK8,X2)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK8,X2),sK10)
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK8,X2))
      | ~ sP4(sK7,sK8,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f163,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( sK10 = k3_tmap_1(X0,sK7,X1,sK8,X2)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK8,X2),sK10)
      | ~ v1_funct_2(k3_tmap_1(X0,sK7,X1,sK8,X2),u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK8,X2))
      | ~ sP4(sK7,sK8,X2,X1,X0) ) ),
    inference(resolution,[],[f149,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      | sK10 = X0
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),X0,sK10)
      | ~ v1_funct_2(X0,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f148,f71])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),X0,sK10)
      | sK10 = X0
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      | ~ v1_funct_2(X0,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f141,f72])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK7),X0,sK10)
      | sK10 = X0
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK7))))
      | ~ v1_funct_2(X0,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f105,f74])).

fof(f105,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f254,plain,(
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
    inference(subsumption_resolution,[],[f253,f111])).

fof(f253,plain,(
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
    inference(subsumption_resolution,[],[f234,f112])).

fof(f234,plain,(
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
    inference(resolution,[],[f110,f113])).

fof(f110,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f226,plain,
    ( sP2(sK11,sK10,sK9,sK8,sK7,sK6)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f224])).

fof(f697,plain,(
    spl12_14 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | spl12_14 ),
    inference(subsumption_resolution,[],[f695,f58])).

fof(f695,plain,
    ( v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f694,f60])).

fof(f694,plain,
    ( ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f693,f64])).

fof(f693,plain,
    ( v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f692,f66])).

fof(f692,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f691,f67])).

fof(f691,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(subsumption_resolution,[],[f690,f69])).

fof(f690,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_14 ),
    inference(resolution,[],[f688,f104])).

fof(f104,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f688,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | spl12_14 ),
    inference(avatar_component_clause,[],[f686])).

fof(f689,plain,
    ( spl12_13
    | ~ spl12_14
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f667,f224,f686,f682])).

fof(f667,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f666,f69])).

fof(f666,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f665,f58])).

fof(f665,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f664,f59])).

fof(f664,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f663,f60])).

fof(f663,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f661,f66])).

fof(f661,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(k1_tsep_1(sK6,sK8,sK9),sK6)
    | sK11 = k3_tmap_1(sK6,sK7,k1_tsep_1(sK6,sK8,sK9),sK9,k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl12_2 ),
    inference(resolution,[],[f226,f513])).

fof(f513,plain,(
    ! [X0] :
      ( ~ sP2(sK11,sK10,sK9,sK8,sK7,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,sK8,sK9),X0)
      | sK11 = k3_tmap_1(X0,sK7,k1_tsep_1(X0,sK8,sK9),sK9,k10_tmap_1(X0,sK7,sK8,sK9,sK10,sK11))
      | ~ m1_pre_topc(sK9,X0) ) ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,(
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
      | ~ sP2(sK11,sK10,sK9,sK8,sK7,X0) ) ),
    inference(resolution,[],[f491,f335])).

fof(f335,plain,(
    ! [X10,X11,X9] :
      ( ~ sP5(sK7,sK9,X10,X9,sK11,X11)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,sK9),X9)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(sK9,X9)
      | sK11 = k3_tmap_1(X9,sK7,k1_tsep_1(X9,X10,sK9),sK9,k10_tmap_1(X9,sK7,X10,sK9,X11,sK11))
      | ~ sP2(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(subsumption_resolution,[],[f334,f61])).

fof(f334,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_pre_topc(sK9,X9)
      | ~ m1_pre_topc(k1_tsep_1(X9,X10,sK9),X9)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ sP5(sK7,sK9,X10,X9,sK11,X11)
      | sK11 = k3_tmap_1(X9,sK7,k1_tsep_1(X9,X10,sK9),sK9,k10_tmap_1(X9,sK7,X10,sK9,X11,sK11))
      | ~ sP2(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(subsumption_resolution,[],[f333,f62])).

fof(f333,plain,(
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
      | ~ sP2(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(subsumption_resolution,[],[f322,f63])).

fof(f322,plain,(
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
      | ~ sP2(sK11,X11,sK9,X10,sK7,X9) ) ),
    inference(resolution,[],[f254,f185])).

fof(f185,plain,(
    ! [X4,X5,X3] :
      ( ~ sP4(sK7,sK9,k10_tmap_1(X3,sK7,X4,sK9,X5,sK11),k1_tsep_1(X3,X4,sK9),X3)
      | sK11 = k3_tmap_1(X3,sK7,k1_tsep_1(X3,X4,sK9),sK9,k10_tmap_1(X3,sK7,X4,sK9,X5,sK11))
      | ~ sP2(sK11,X5,sK9,X4,sK7,X3) ) ),
    inference(resolution,[],[f177,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK9,X2),sK11)
      | sK11 = k3_tmap_1(X0,sK7,X1,sK9,X2)
      | ~ sP4(sK7,sK9,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f176,f107])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK7,X1,sK9,X2)
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK9,X2),sK11)
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK9,X2))
      | ~ sP4(sK7,sK9,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f173,f108])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK7,X1,sK9,X2)
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),k3_tmap_1(X0,sK7,X1,sK9,X2),sK11)
      | ~ v1_funct_2(k3_tmap_1(X0,sK7,X1,sK9,X2),u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(k3_tmap_1(X0,sK7,X1,sK9,X2))
      | ~ sP4(sK7,sK9,X2,X1,X0) ) ),
    inference(resolution,[],[f151,f109])).

fof(f151,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | sK11 = X1
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),X1,sK11)
      | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f150,f75])).

fof(f150,plain,(
    ! [X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),X1,sK11)
      | sK11 = X1
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f142,f76])).

fof(f142,plain,(
    ! [X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK7),X1,sK11)
      | sK11 = X1
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f105,f78])).

fof(f660,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f658,f58])).

fof(f658,plain,
    ( v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f657,f59])).

fof(f657,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f656,f60])).

fof(f656,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f655,f66])).

fof(f655,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f654,f69])).

fof(f654,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_1 ),
    inference(resolution,[],[f640,f222])).

fof(f222,plain,
    ( ~ sP3(sK11,sK9,sK8,sK6,sK7,sK10)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl12_1
  <=> sP3(sK11,sK9,sK8,sK6,sK7,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f640,plain,(
    ! [X0] :
      ( sP3(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f639,f64])).

fof(f639,plain,(
    ! [X0] :
      ( sP3(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f638,f70])).

fof(f70,plain,(
    ~ r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f40])).

fof(f638,plain,(
    ! [X0] :
      ( sP3(sK11,sK9,sK8,X0,sK7,sK10)
      | r1_tsep_1(sK8,sK9)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f637,f71])).

fof(f637,plain,(
    ! [X0] :
      ( sP3(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ v1_funct_1(sK10)
      | r1_tsep_1(sK8,sK9)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f629,f72])).

fof(f629,plain,(
    ! [X0] :
      ( sP3(sK11,sK9,sK8,X0,sK7,sK10)
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK7))
      | ~ v1_funct_1(sK10)
      | r1_tsep_1(sK8,sK9)
      | ~ m1_pre_topc(sK9,X0)
      | ~ m1_pre_topc(sK8,X0)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f578,f74])).

fof(f578,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
      | sP3(sK11,sK9,X3,X4,sK7,X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK7))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK9)
      | ~ m1_pre_topc(sK9,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f577,f61])).

fof(f577,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK11,sK9,X3,X4,sK7,X5)
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
    inference(subsumption_resolution,[],[f576,f62])).

fof(f576,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK11,sK9,X3,X4,sK7,X5)
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
    inference(subsumption_resolution,[],[f575,f63])).

fof(f575,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK11,sK9,X3,X4,sK7,X5)
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
    inference(subsumption_resolution,[],[f574,f67])).

fof(f574,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK11,sK9,X3,X4,sK7,X5)
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
    inference(subsumption_resolution,[],[f573,f75])).

fof(f573,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK11,sK9,X3,X4,sK7,X5)
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
    inference(subsumption_resolution,[],[f561,f76])).

fof(f561,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK11,sK9,X3,X4,sK7,X5)
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
    inference(resolution,[],[f102,f78])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP3(X5,X3,X2,X0,X1,X4)
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( sP3(X5,X3,X2,X0,X1,X4)
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
    inference(definition_folding,[],[f15,f28,f27])).

fof(f28,plain,(
    ! [X5,X3,X2,X0,X1,X4] :
      ( ( sP2(X5,X4,X3,X2,X1,X0)
      <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
      | ~ sP3(X5,X3,X2,X0,X1,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_tmap_1)).

fof(f528,plain,(
    spl12_4 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl12_4 ),
    inference(subsumption_resolution,[],[f526,f58])).

fof(f526,plain,
    ( v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f525,f59])).

fof(f525,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f524,f60])).

fof(f524,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f523,f66])).

fof(f523,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f522,f69])).

fof(f522,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_4 ),
    inference(resolution,[],[f521,f491])).

fof(f521,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_4 ),
    inference(resolution,[],[f351,f112])).

fof(f351,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl12_4
  <=> v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f519,plain,(
    spl12_3 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl12_3 ),
    inference(subsumption_resolution,[],[f517,f58])).

fof(f517,plain,
    ( v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f516,f59])).

fof(f516,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f515,f60])).

fof(f515,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f514,f66])).

fof(f514,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f511,f69])).

fof(f511,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl12_3 ),
    inference(resolution,[],[f491,f361])).

fof(f361,plain,
    ( ~ sP5(sK7,sK9,sK8,sK6,sK11,sK10)
    | spl12_3 ),
    inference(resolution,[],[f347,f111])).

fof(f347,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl12_3
  <=> v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f360,plain,
    ( ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f80,f357,f353,f349,f345])).

fof(f80,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),k1_tsep_1(sK6,sK8,sK9),sK7)
    | ~ v1_funct_2(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11),u1_struct_0(k1_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7))
    | ~ v1_funct_1(k10_tmap_1(sK6,sK7,sK8,sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f40])).

fof(f227,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f215,f224,f220])).

fof(f215,plain,
    ( sP2(sK11,sK10,sK9,sK8,sK7,sK6)
    | ~ sP3(sK11,sK9,sK8,sK6,sK7,sK10) ),
    inference(resolution,[],[f98,f79])).

fof(f79,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK6,sK8,sK9)),u1_struct_0(sK7),k3_tmap_1(sK6,sK7,sK8,k2_tsep_1(sK6,sK8,sK9),sK10),k3_tmap_1(sK6,sK7,sK9,k2_tsep_1(sK6,sK8,sK9),sK11)) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0))
      | sP2(X0,X5,X1,X2,X4,X3)
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( sP2(X0,X5,X1,X2,X4,X3)
          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0)) )
        & ( r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0))
          | ~ sP2(X0,X5,X1,X2,X4,X3) ) )
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X5,X3,X2,X0,X1,X4] :
      ( ( ( sP2(X5,X4,X3,X2,X1,X0)
          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
        & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          | ~ sP2(X5,X4,X3,X2,X1,X0) ) )
      | ~ sP3(X5,X3,X2,X0,X1,X4) ) ),
    inference(nnf_transformation,[],[f28])).

%------------------------------------------------------------------------------

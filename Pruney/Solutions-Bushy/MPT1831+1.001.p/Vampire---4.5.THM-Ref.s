%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1831+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.48s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  244 (1894 expanded)
%              Number of leaves         :   27 ( 951 expanded)
%              Depth                    :   60
%              Number of atoms          : 1993 (46985 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1772,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f303,f706,f715,f1011,f1749,f1766,f1771])).

fof(f1771,plain,
    ( spl13_4
    | ~ spl13_18 ),
    inference(avatar_contradiction_clause,[],[f1770])).

fof(f1770,plain,
    ( $false
    | spl13_4
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f1768,f1753])).

fof(f1753,plain,
    ( sP6(sK8,sK10,sK9,sK7,sK12,sK11)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f1752,plain,
    ( spl13_18
  <=> sP6(sK8,sK10,sK9,sK7,sK12,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f1768,plain,
    ( ~ sP6(sK8,sK10,sK9,sK7,sK12,sK11)
    | spl13_4 ),
    inference(resolution,[],[f137,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP6(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP6(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP6(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP6(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f137,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
    | spl13_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl13_4
  <=> m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f1766,plain,(
    spl13_18 ),
    inference(avatar_contradiction_clause,[],[f1765])).

fof(f1765,plain,
    ( $false
    | spl13_18 ),
    inference(subsumption_resolution,[],[f1764,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
      | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(sK7,sK9,sK10),sK8)
      | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
      | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12)) )
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),sK11),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),sK12))
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
    & v5_pre_topc(sK12,sK10,sK8)
    & v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
    & v1_funct_1(sK12)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
    & v5_pre_topc(sK11,sK9,sK8)
    & v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
    & v1_funct_1(sK11)
    & ~ r1_tsep_1(sK9,sK10)
    & m1_pre_topc(sK10,sK7)
    & v1_tsep_1(sK10,sK7)
    & ~ v2_struct_0(sK10)
    & m1_pre_topc(sK9,sK7)
    & v1_tsep_1(sK9,sK7)
    & ~ v2_struct_0(sK9)
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f10,f40,f39,f38,f37,f36,f35])).

fof(f35,plain,
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK7,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK7,X1,X2,X3,X4,X5),k1_tsep_1(sK7,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK7,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK7,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK7,X1,X2,k2_tsep_1(sK7,X2,X3),X4),k3_tmap_1(sK7,X1,X3,k2_tsep_1(sK7,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,sK7)
                  & v1_tsep_1(X3,sK7)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK7)
              & v1_tsep_1(X2,sK7)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK7,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK7,X1,X2,X3,X4,X5),k1_tsep_1(sK7,X2,X3),X1)
                          | ~ v1_funct_2(k10_tmap_1(sK7,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK7,X1,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK7,X1,X2,k2_tsep_1(sK7,X2,X3),X4),k3_tmap_1(sK7,X1,X3,k2_tsep_1(sK7,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,sK7)
                & v1_tsep_1(X3,sK7)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK7)
            & v1_tsep_1(X2,sK7)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(sK8))))
                        | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,X2,X3,X4,X5),k1_tsep_1(sK7,X2,X3),sK8)
                        | ~ v1_funct_2(k10_tmap_1(sK7,sK8,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(sK8))
                        | ~ v1_funct_1(k10_tmap_1(sK7,sK8,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,X2,X3)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,X2,k2_tsep_1(sK7,X2,X3),X4),k3_tmap_1(sK7,sK8,X3,k2_tsep_1(sK7,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
                      & v5_pre_topc(X5,X3,sK8)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK8))))
                  & v5_pre_topc(X4,X2,sK8)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK8))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,sK7)
              & v1_tsep_1(X3,sK7)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK7)
          & v1_tsep_1(X2,sK7)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(sK8))))
                      | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,X2,X3,X4,X5),k1_tsep_1(sK7,X2,X3),sK8)
                      | ~ v1_funct_2(k10_tmap_1(sK7,sK8,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK7,X2,X3)),u1_struct_0(sK8))
                      | ~ v1_funct_1(k10_tmap_1(sK7,sK8,X2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,X2,X3)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,X2,k2_tsep_1(sK7,X2,X3),X4),k3_tmap_1(sK7,sK8,X3,k2_tsep_1(sK7,X2,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
                    & v5_pre_topc(X5,X3,sK8)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK8))))
                & v5_pre_topc(X4,X2,sK8)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK8))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(X2,X3)
            & m1_pre_topc(X3,sK7)
            & v1_tsep_1(X3,sK7)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK7)
        & v1_tsep_1(X2,sK7)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,X3)),u1_struct_0(sK8))))
                    | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5),k1_tsep_1(sK7,sK9,X3),sK8)
                    | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5),u1_struct_0(k1_tsep_1(sK7,sK9,X3)),u1_struct_0(sK8))
                    | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,X3)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,X3),X4),k3_tmap_1(sK7,sK8,X3,k2_tsep_1(sK7,sK9,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
                  & v5_pre_topc(X5,X3,sK8)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
              & v5_pre_topc(X4,sK9,sK8)
              & v1_funct_2(X4,u1_struct_0(sK9),u1_struct_0(sK8))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(sK9,X3)
          & m1_pre_topc(X3,sK7)
          & v1_tsep_1(X3,sK7)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK9,sK7)
      & v1_tsep_1(sK9,sK7)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,X3)),u1_struct_0(sK8))))
                  | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5),k1_tsep_1(sK7,sK9,X3),sK8)
                  | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5),u1_struct_0(k1_tsep_1(sK7,sK9,X3)),u1_struct_0(sK8))
                  | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,X3,X4,X5)) )
                & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,X3)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,X3),X4),k3_tmap_1(sK7,sK8,X3,k2_tsep_1(sK7,sK9,X3),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
                & v5_pre_topc(X5,X3,sK8)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
            & v5_pre_topc(X4,sK9,sK8)
            & v1_funct_2(X4,u1_struct_0(sK9),u1_struct_0(sK8))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(sK9,X3)
        & m1_pre_topc(X3,sK7)
        & v1_tsep_1(X3,sK7)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
                | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5),k1_tsep_1(sK7,sK9,sK10),sK8)
                | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
                | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5)) )
              & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),X4),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
              & v5_pre_topc(X5,sK10,sK8)
              & v1_funct_2(X5,u1_struct_0(sK10),u1_struct_0(sK8))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
          & v5_pre_topc(X4,sK9,sK8)
          & v1_funct_2(X4,u1_struct_0(sK9),u1_struct_0(sK8))
          & v1_funct_1(X4) )
      & ~ r1_tsep_1(sK9,sK10)
      & m1_pre_topc(sK10,sK7)
      & v1_tsep_1(sK10,sK7)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
              | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5),k1_tsep_1(sK7,sK9,sK10),sK8)
              | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
              | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,X4,X5)) )
            & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),X4),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
            & v5_pre_topc(X5,sK10,sK8)
            & v1_funct_2(X5,u1_struct_0(sK10),u1_struct_0(sK8))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
        & v5_pre_topc(X4,sK9,sK8)
        & v1_funct_2(X4,u1_struct_0(sK9),u1_struct_0(sK8))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
            | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5),k1_tsep_1(sK7,sK9,sK10),sK8)
            | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
            | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5)) )
          & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),sK11),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
          & v5_pre_topc(X5,sK10,sK8)
          & v1_funct_2(X5,u1_struct_0(sK10),u1_struct_0(sK8))
          & v1_funct_1(X5) )
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
      & v5_pre_topc(sK11,sK9,sK8)
      & v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
          | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5),k1_tsep_1(sK7,sK9,sK10),sK8)
          | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
          | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,X5)) )
        & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),sK11),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
        & v5_pre_topc(X5,sK10,sK8)
        & v1_funct_2(X5,u1_struct_0(sK10),u1_struct_0(sK8))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
        | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(sK7,sK9,sK10),sK8)
        | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
        | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12)) )
      & r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),sK11),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),sK12))
      & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
      & v5_pre_topc(sK12,sK10,sK8)
      & v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      & v1_funct_1(sK12) ) ),
    introduced(choice_axiom,[])).

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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_tmap_1)).

fof(f1764,plain,
    ( v2_struct_0(sK7)
    | spl13_18 ),
    inference(subsumption_resolution,[],[f1763,f62])).

fof(f62,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1763,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_18 ),
    inference(subsumption_resolution,[],[f1762,f63])).

fof(f63,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1762,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_18 ),
    inference(subsumption_resolution,[],[f1761,f69])).

fof(f69,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1761,plain,
    ( ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_18 ),
    inference(subsumption_resolution,[],[f1760,f72])).

fof(f72,plain,(
    m1_pre_topc(sK10,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1760,plain,
    ( ~ m1_pre_topc(sK10,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_18 ),
    inference(resolution,[],[f1754,f686])).

fof(f686,plain,(
    ! [X0] :
      ( sP6(sK8,sK10,sK9,X0,sK12,sK11)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f685,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f41])).

fof(f685,plain,(
    ! [X0] :
      ( sP6(sK8,sK10,sK9,X0,sK12,sK11)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f684,f74])).

fof(f74,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f41])).

fof(f684,plain,(
    ! [X0] :
      ( sP6(sK8,sK10,sK9,X0,sK12,sK11)
      | ~ v1_funct_1(sK11)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f676,f75])).

fof(f75,plain,(
    v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f41])).

fof(f676,plain,(
    ! [X0] :
      ( sP6(sK8,sK10,sK9,X0,sK12,sK11)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(sK11)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f585,f77])).

fof(f77,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f585,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f584,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f584,plain,(
    ! [X4,X5,X3] :
      ( sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f583,f65])).

fof(f65,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f583,plain,(
    ! [X4,X5,X3] :
      ( sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f582,f66])).

fof(f66,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f582,plain,(
    ! [X4,X5,X3] :
      ( sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f581,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f41])).

fof(f581,plain,(
    ! [X4,X5,X3] :
      ( sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f580,f78])).

fof(f78,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f41])).

fof(f580,plain,(
    ! [X4,X5,X3] :
      ( sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ v1_funct_1(sK12)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f568,f79])).

fof(f79,plain,(
    v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f41])).

fof(f568,plain,(
    ! [X4,X5,X3] :
      ( sP6(sK8,sK10,X3,X4,sK12,X5)
      | ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK10,X4)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f119,f81])).

fof(f81,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f119,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP6(X1,X3,X2,X0,X5,X4)
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP6(X1,X3,X2,X0,X5,X4)
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
    inference(definition_folding,[],[f22,f33])).

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
    inference(flattening,[],[f21])).

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

fof(f1754,plain,
    ( ~ sP6(sK8,sK10,sK9,sK7,sK12,sK11)
    | spl13_18 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f1749,plain,
    ( spl13_3
    | ~ spl13_6 ),
    inference(avatar_contradiction_clause,[],[f1748])).

fof(f1748,plain,
    ( $false
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1747,f61])).

fof(f1747,plain,
    ( v2_struct_0(sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1746,f63])).

fof(f1746,plain,
    ( ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1745,f67])).

fof(f1745,plain,
    ( v2_struct_0(sK9)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1744,f69])).

fof(f1744,plain,
    ( ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1743,f70])).

fof(f1743,plain,
    ( v2_struct_0(sK10)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1742,f72])).

fof(f1742,plain,
    ( ~ m1_pre_topc(sK10,sK7)
    | v2_struct_0(sK10)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(resolution,[],[f1741,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f1741,plain,
    ( ~ sP4(sK7,sK10,sK9)
    | spl13_3
    | ~ spl13_6 ),
    inference(resolution,[],[f1740,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f1740,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f1739,f302])).

fof(f302,plain,
    ( sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl13_6
  <=> sP2(sK12,sK11,sK10,sK9,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f1739,plain,
    ( ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1738,f61])).

fof(f1738,plain,
    ( v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1737,f62])).

fof(f1737,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1736,f63])).

fof(f1736,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1735,f68])).

fof(f68,plain,(
    v1_tsep_1(sK9,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1735,plain,
    ( ~ v1_tsep_1(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1734,f69])).

fof(f1734,plain,
    ( ~ m1_pre_topc(sK9,sK7)
    | ~ v1_tsep_1(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1733,f71])).

fof(f71,plain,(
    v1_tsep_1(sK10,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1733,plain,
    ( ~ v1_tsep_1(sK10,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v1_tsep_1(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(subsumption_resolution,[],[f1731,f72])).

fof(f1731,plain,
    ( ~ m1_pre_topc(sK10,sK7)
    | ~ v1_tsep_1(sK10,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ v1_tsep_1(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK9,sK10),sK7)
    | spl13_3 ),
    inference(resolution,[],[f1726,f716])).

fof(f716,plain,
    ( ~ sP0(sK8,sK10,sK9,sK7,k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12))
    | spl13_3 ),
    inference(resolution,[],[f133,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f133,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(sK7,sK9,sK10),sK8)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl13_3
  <=> v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(sK7,sK9,sK10),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f1726,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(subsumption_resolution,[],[f1725,f686])).

fof(f1725,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(subsumption_resolution,[],[f1724,f64])).

fof(f1724,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(subsumption_resolution,[],[f1723,f65])).

fof(f1723,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(subsumption_resolution,[],[f1722,f66])).

fof(f1722,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(subsumption_resolution,[],[f1721,f67])).

fof(f1721,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(subsumption_resolution,[],[f1701,f70])).

fof(f1701,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18) ) ),
    inference(duplicate_literal_removal,[],[f1696])).

fof(f1696,plain,(
    ! [X18] :
      ( sP0(sK8,sK10,sK9,X18,k10_tmap_1(X18,sK8,sK9,sK10,sK11,sK12))
      | ~ m1_pre_topc(sK10,X18)
      | ~ v1_tsep_1(sK10,X18)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(sK9,X18)
      | ~ v1_tsep_1(sK9,X18)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ sP6(sK8,sK10,sK9,X18,sK12,sK11)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X18)
      | ~ m1_pre_topc(sK10,X18)
      | ~ m1_pre_topc(k1_tsep_1(X18,sK9,sK10),X18)
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | v2_struct_0(X18)
      | ~ m1_pre_topc(sK9,X18) ) ),
    inference(resolution,[],[f806,f1510])).

fof(f1510,plain,(
    ! [X1] :
      ( sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK9,X1) ) ),
    inference(subsumption_resolution,[],[f1509,f686])).

fof(f1509,plain,(
    ! [X1] :
      ( ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11)
      | ~ m1_pre_topc(sK9,X1) ) ),
    inference(subsumption_resolution,[],[f1508,f64])).

fof(f1508,plain,(
    ! [X1] :
      ( ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11)
      | ~ m1_pre_topc(sK9,X1)
      | v2_struct_0(sK8) ) ),
    inference(subsumption_resolution,[],[f1507,f65])).

fof(f1507,plain,(
    ! [X1] :
      ( ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11)
      | ~ m1_pre_topc(sK9,X1)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8) ) ),
    inference(subsumption_resolution,[],[f1501,f66])).

fof(f1501,plain,(
    ! [X1] :
      ( ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11)
      | ~ m1_pre_topc(sK9,X1)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8) ) ),
    inference(duplicate_literal_removal,[],[f1500])).

fof(f1500,plain,(
    ! [X1] :
      ( ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11)
      | ~ m1_pre_topc(sK9,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11) ) ),
    inference(resolution,[],[f1452,f423])).

fof(f423,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34,X32] :
      ( sP5(X32,X33,k10_tmap_1(X34,X32,X35,X36,X37,X38),k1_tsep_1(X34,X35,X36),X39)
      | ~ m1_pre_topc(X33,X39)
      | ~ m1_pre_topc(k1_tsep_1(X34,X35,X36),X39)
      | ~ l1_pre_topc(X32)
      | ~ v2_pre_topc(X32)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(X39)
      | ~ v2_pre_topc(X39)
      | v2_struct_0(X39)
      | ~ sP6(X32,X36,X35,X34,X38,X37) ) ),
    inference(subsumption_resolution,[],[f422,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP6(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f422,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34,X32] :
      ( sP5(X32,X33,k10_tmap_1(X34,X32,X35,X36,X37,X38),k1_tsep_1(X34,X35,X36),X39)
      | ~ v1_funct_1(k10_tmap_1(X34,X32,X35,X36,X37,X38))
      | ~ m1_pre_topc(X33,X39)
      | ~ m1_pre_topc(k1_tsep_1(X34,X35,X36),X39)
      | ~ l1_pre_topc(X32)
      | ~ v2_pre_topc(X32)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(X39)
      | ~ v2_pre_topc(X39)
      | v2_struct_0(X39)
      | ~ sP6(X32,X36,X35,X34,X38,X37) ) ),
    inference(subsumption_resolution,[],[f403,f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP6(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f403,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34,X32] :
      ( sP5(X32,X33,k10_tmap_1(X34,X32,X35,X36,X37,X38),k1_tsep_1(X34,X35,X36),X39)
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
      | ~ sP6(X32,X36,X35,X34,X38,X37) ) ),
    inference(resolution,[],[f115,f118])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP5(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP5(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f20,f31])).

fof(f31,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP5(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

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
    inference(flattening,[],[f19])).

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

fof(f1452,plain,(
    ! [X1] :
      ( ~ sP5(sK8,sK9,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X1,sK9,sK10),X1)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11) ) ),
    inference(subsumption_resolution,[],[f1451,f64])).

fof(f1451,plain,(
    ! [X1] :
      ( ~ sP5(sK8,sK9,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X1,sK9,sK10),X1)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11) ) ),
    inference(subsumption_resolution,[],[f1450,f65])).

fof(f1450,plain,(
    ! [X1] :
      ( ~ sP5(sK8,sK9,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X1,sK9,sK10),X1)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11) ) ),
    inference(subsumption_resolution,[],[f1446,f66])).

fof(f1446,plain,(
    ! [X1] :
      ( ~ sP5(sK8,sK9,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X1,sK9,sK10),X1)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X1)
      | sP1(sK8,sK10,k10_tmap_1(X1,sK8,sK9,sK10,sK11,sK12),sK9,X1)
      | ~ m1_pre_topc(sK10,X1)
      | ~ m1_pre_topc(k1_tsep_1(X1,sK9,sK10),X1)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP6(sK8,sK10,sK9,X1,sK12,sK11) ) ),
    inference(resolution,[],[f1428,f423])).

fof(f1428,plain,(
    ! [X8] :
      ( ~ sP5(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP5(sK8,sK9,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8)
      | sP1(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),sK9,X8) ) ),
    inference(subsumption_resolution,[],[f1427,f78])).

fof(f1427,plain,(
    ! [X8] :
      ( ~ v1_funct_1(sK12)
      | sP1(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),sK9,X8)
      | ~ sP5(sK8,sK9,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8)
      | ~ sP5(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8) ) ),
    inference(subsumption_resolution,[],[f1426,f79])).

fof(f1426,plain,(
    ! [X8] :
      ( ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | sP1(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),sK9,X8)
      | ~ sP5(sK8,sK9,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8)
      | ~ sP5(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8) ) ),
    inference(subsumption_resolution,[],[f1425,f80])).

fof(f80,plain,(
    v5_pre_topc(sK12,sK10,sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f1425,plain,(
    ! [X8] :
      ( ~ v5_pre_topc(sK12,sK10,sK8)
      | ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | sP1(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),sK9,X8)
      | ~ sP5(sK8,sK9,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8)
      | ~ sP5(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8) ) ),
    inference(subsumption_resolution,[],[f1410,f81])).

fof(f1410,plain,(
    ! [X8] :
      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
      | ~ v5_pre_topc(sK12,sK10,sK8)
      | ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | sP1(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),sK9,X8)
      | ~ sP5(sK8,sK9,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8)
      | ~ sP5(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8) ) ),
    inference(duplicate_literal_removal,[],[f1407])).

fof(f1407,plain,(
    ! [X8] :
      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
      | ~ v5_pre_topc(sK12,sK10,sK8)
      | ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | sP1(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),sK9,X8)
      | ~ sP5(sK8,sK9,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8)
      | ~ sP5(sK8,sK10,k10_tmap_1(X8,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(X8,sK9,sK10),X8)
      | ~ sP2(sK12,sK11,sK10,sK9,sK8,X8) ) ),
    inference(superposition,[],[f963,f220])).

fof(f220,plain,(
    ! [X4,X5,X3] :
      ( sK12 = k3_tmap_1(X3,sK8,k1_tsep_1(X3,X4,sK10),sK10,k10_tmap_1(X3,sK8,X4,sK10,X5,sK12))
      | ~ sP5(sK8,sK10,k10_tmap_1(X3,sK8,X4,sK10,X5,sK12),k1_tsep_1(X3,X4,sK10),X3)
      | ~ sP2(sK12,X5,sK10,X4,sK8,X3) ) ),
    inference(resolution,[],[f212,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP2(X0,X1,X2,X3,X4,X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1) )
      & ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X2,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X0)
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1) )
        | ~ sP2(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X5,X4,X3,X2,X1,X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
      & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
        | ~ sP2(X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X5,X4,X3,X2,X1,X0)
        | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
      & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
        | ~ sP2(X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( sP2(X5,X4,X3,X2,X1,X0)
    <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK10),u1_struct_0(sK8),k3_tmap_1(X0,sK8,X1,sK10,X2),sK12)
      | sK12 = k3_tmap_1(X0,sK8,X1,sK10,X2)
      | ~ sP5(sK8,sK10,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f211,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP5(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP5(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP5(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( sK12 = k3_tmap_1(X0,sK8,X1,sK10,X2)
      | ~ r2_funct_2(u1_struct_0(sK10),u1_struct_0(sK8),k3_tmap_1(X0,sK8,X1,sK10,X2),sK12)
      | ~ v1_funct_1(k3_tmap_1(X0,sK8,X1,sK10,X2))
      | ~ sP5(sK8,sK10,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f208,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP5(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( sK12 = k3_tmap_1(X0,sK8,X1,sK10,X2)
      | ~ r2_funct_2(u1_struct_0(sK10),u1_struct_0(sK8),k3_tmap_1(X0,sK8,X1,sK10,X2),sK12)
      | ~ v1_funct_2(k3_tmap_1(X0,sK8,X1,sK10,X2),u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X0,sK8,X1,sK10,X2))
      | ~ sP5(sK8,sK10,X2,X1,X0) ) ),
    inference(resolution,[],[f171,f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP5(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f171,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
      | sK12 = X1
      | ~ r2_funct_2(u1_struct_0(sK10),u1_struct_0(sK8),X1,sK12)
      | ~ v1_funct_2(X1,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f170,f78])).

fof(f170,plain,(
    ! [X1] :
      ( ~ r2_funct_2(u1_struct_0(sK10),u1_struct_0(sK8),X1,sK12)
      | sK12 = X1
      | ~ v1_funct_1(sK12)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
      | ~ v1_funct_2(X1,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f162,f79])).

fof(f162,plain,(
    ! [X1] :
      ( ~ r2_funct_2(u1_struct_0(sK10),u1_struct_0(sK8),X1,sK12)
      | sK12 = X1
      | ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK8))))
      | ~ v1_funct_2(X1,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f110,f81])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

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

fof(f963,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK8))))
      | ~ v5_pre_topc(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),X7,sK8)
      | ~ v1_funct_2(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),u1_struct_0(X7),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)))
      | sP1(sK8,X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),sK9,X6)
      | ~ sP5(sK8,sK9,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),k1_tsep_1(X6,sK9,X7),X6)
      | ~ sP2(X8,sK11,X7,sK9,sK8,X6) ) ),
    inference(subsumption_resolution,[],[f962,f74])).

fof(f962,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK8))))
      | ~ v5_pre_topc(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),X7,sK8)
      | ~ v1_funct_2(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),u1_struct_0(X7),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)))
      | sP1(sK8,X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),sK9,X6)
      | ~ v1_funct_1(sK11)
      | ~ sP5(sK8,sK9,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),k1_tsep_1(X6,sK9,X7),X6)
      | ~ sP2(X8,sK11,X7,sK9,sK8,X6) ) ),
    inference(subsumption_resolution,[],[f961,f75])).

fof(f961,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK8))))
      | ~ v5_pre_topc(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),X7,sK8)
      | ~ v1_funct_2(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),u1_struct_0(X7),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)))
      | sP1(sK8,X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),sK9,X6)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(sK11)
      | ~ sP5(sK8,sK9,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),k1_tsep_1(X6,sK9,X7),X6)
      | ~ sP2(X8,sK11,X7,sK9,sK8,X6) ) ),
    inference(subsumption_resolution,[],[f960,f76])).

fof(f76,plain,(
    v5_pre_topc(sK11,sK9,sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f960,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK8))))
      | ~ v5_pre_topc(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),X7,sK8)
      | ~ v1_funct_2(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),u1_struct_0(X7),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)))
      | sP1(sK8,X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),sK9,X6)
      | ~ v5_pre_topc(sK11,sK9,sK8)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(sK11)
      | ~ sP5(sK8,sK9,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),k1_tsep_1(X6,sK9,X7),X6)
      | ~ sP2(X8,sK11,X7,sK9,sK8,X6) ) ),
    inference(subsumption_resolution,[],[f939,f77])).

fof(f939,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
      | ~ m1_subset_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK8))))
      | ~ v5_pre_topc(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),X7,sK8)
      | ~ v1_funct_2(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)),u1_struct_0(X7),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X6,sK8,k1_tsep_1(X6,sK9,X7),X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8)))
      | sP1(sK8,X7,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),sK9,X6)
      | ~ v5_pre_topc(sK11,sK9,sK8)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(sK11)
      | ~ sP5(sK8,sK9,k10_tmap_1(X6,sK8,sK9,X7,sK11,X8),k1_tsep_1(X6,sK9,X7),X6)
      | ~ sP2(X8,sK11,X7,sK9,sK8,X6) ) ),
    inference(superposition,[],[f92,f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK8,k1_tsep_1(X0,sK9,X1),sK9,k10_tmap_1(X0,sK8,sK9,X1,sK11,X2))
      | ~ sP5(sK8,sK9,k10_tmap_1(X0,sK8,sK9,X1,sK11,X2),k1_tsep_1(X0,sK9,X1),X0)
      | ~ sP2(X2,sK11,X1,sK9,sK8,X0) ) ),
    inference(resolution,[],[f202,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k3_tmap_1(X5,X4,k1_tsep_1(X5,X3,X2),X3,k10_tmap_1(X5,X4,X3,X2,X1,X0)),X1)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK8),k3_tmap_1(X0,sK8,X1,sK9,X2),sK11)
      | sK11 = k3_tmap_1(X0,sK8,X1,sK9,X2)
      | ~ sP5(sK8,sK9,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f201,f112])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK8,X1,sK9,X2)
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK8),k3_tmap_1(X0,sK8,X1,sK9,X2),sK11)
      | ~ v1_funct_1(k3_tmap_1(X0,sK8,X1,sK9,X2))
      | ~ sP5(sK8,sK9,X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f198,f113])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( sK11 = k3_tmap_1(X0,sK8,X1,sK9,X2)
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK8),k3_tmap_1(X0,sK8,X1,sK9,X2),sK11)
      | ~ v1_funct_2(k3_tmap_1(X0,sK8,X1,sK9,X2),u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(k3_tmap_1(X0,sK8,X1,sK9,X2))
      | ~ sP5(sK8,sK9,X2,X1,X0) ) ),
    inference(resolution,[],[f169,f114])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
      | sK11 = X0
      | ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK8),X0,sK11)
      | ~ v1_funct_2(X0,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f168,f74])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK8),X0,sK11)
      | sK11 = X0
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
      | ~ v1_funct_2(X0,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f161,f75])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK9),u1_struct_0(sK8),X0,sK11)
      | sK11 = X0
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(sK11)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
      | ~ v1_funct_2(X0,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f110,f77])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f806,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP1(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP0(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ m1_pre_topc(X27,X28)
      | ~ v1_tsep_1(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_tsep_1(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP6(X26,X27,X29,X28,X31,X30) ) ),
    inference(subsumption_resolution,[],[f805,f116])).

fof(f805,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP1(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP0(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ v1_funct_1(k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ m1_pre_topc(X27,X28)
      | ~ v1_tsep_1(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_tsep_1(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP6(X26,X27,X29,X28,X31,X30) ) ),
    inference(subsumption_resolution,[],[f798,f117])).

fof(f798,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( ~ sP1(X26,X27,k10_tmap_1(X28,X26,X29,X27,X30,X31),X29,X28)
      | sP0(X26,X27,X29,X28,k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ v1_funct_2(k10_tmap_1(X28,X26,X29,X27,X30,X31),u1_struct_0(k1_tsep_1(X28,X29,X27)),u1_struct_0(X26))
      | ~ v1_funct_1(k10_tmap_1(X28,X26,X29,X27,X30,X31))
      | ~ m1_pre_topc(X27,X28)
      | ~ v1_tsep_1(X27,X28)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X29,X28)
      | ~ v1_tsep_1(X29,X28)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(X26)
      | ~ v2_pre_topc(X26)
      | v2_struct_0(X26)
      | ~ l1_pre_topc(X28)
      | ~ v2_pre_topc(X28)
      | v2_struct_0(X28)
      | ~ sP6(X26,X27,X29,X28,X31,X30) ) ),
    inference(resolution,[],[f99,f118])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ sP1(X1,X3,X4,X2,X0)
      | sP0(X1,X3,X2,X0,X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_tsep_1(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f24,f23])).

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
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

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
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_tmap_1)).

fof(f1011,plain,(
    spl13_5 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | spl13_5 ),
    inference(subsumption_resolution,[],[f1009,f61])).

fof(f1009,plain,
    ( v2_struct_0(sK7)
    | spl13_5 ),
    inference(subsumption_resolution,[],[f1008,f62])).

fof(f1008,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_5 ),
    inference(subsumption_resolution,[],[f1007,f63])).

fof(f1007,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_5 ),
    inference(subsumption_resolution,[],[f1006,f69])).

fof(f1006,plain,
    ( ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_5 ),
    inference(subsumption_resolution,[],[f1005,f72])).

fof(f1005,plain,
    ( ~ m1_pre_topc(sK10,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_5 ),
    inference(resolution,[],[f983,f298])).

fof(f298,plain,
    ( ~ sP3(sK12,sK10,sK9,sK7,sK8,sK11)
    | spl13_5 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl13_5
  <=> sP3(sK12,sK10,sK9,sK7,sK8,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f983,plain,(
    ! [X0] :
      ( sP3(sK12,sK10,sK9,X0,sK8,sK11)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f982,f67])).

fof(f982,plain,(
    ! [X0] :
      ( sP3(sK12,sK10,sK9,X0,sK8,sK11)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f981,f73])).

fof(f73,plain,(
    ~ r1_tsep_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f41])).

fof(f981,plain,(
    ! [X0] :
      ( sP3(sK12,sK10,sK9,X0,sK8,sK11)
      | r1_tsep_1(sK9,sK10)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f980,f74])).

fof(f980,plain,(
    ! [X0] :
      ( sP3(sK12,sK10,sK9,X0,sK8,sK11)
      | ~ v1_funct_1(sK11)
      | r1_tsep_1(sK9,sK10)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f972,f75])).

fof(f972,plain,(
    ! [X0] :
      ( sP3(sK12,sK10,sK9,X0,sK8,sK11)
      | ~ v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      | ~ v1_funct_1(sK11)
      | r1_tsep_1(sK9,sK10)
      | ~ m1_pre_topc(sK10,X0)
      | ~ m1_pre_topc(sK9,X0)
      | v2_struct_0(sK9)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f828,f77])).

fof(f828,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f827,f64])).

fof(f827,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f826,f65])).

fof(f826,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f825,f66])).

fof(f825,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f824,f70])).

fof(f824,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f823,f78])).

fof(f823,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ v1_funct_1(sK12)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f811,f79])).

fof(f811,plain,(
    ! [X4,X5,X3] :
      ( sP3(sK12,sK10,X3,X4,sK8,X5)
      | ~ v1_funct_2(sK12,u1_struct_0(sK10),u1_struct_0(sK8))
      | ~ v1_funct_1(sK12)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK8))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK8))
      | ~ v1_funct_1(X5)
      | r1_tsep_1(X3,sK10)
      | ~ m1_pre_topc(sK10,X4)
      | v2_struct_0(sK10)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8)
      | v2_struct_0(sK8)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f105,f81])).

fof(f105,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(definition_folding,[],[f14,f27,f26])).

fof(f27,plain,(
    ! [X5,X3,X2,X0,X1,X4] :
      ( ( sP2(X5,X4,X3,X2,X1,X0)
      <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
      | ~ sP3(X5,X3,X2,X0,X1,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
    inference(flattening,[],[f13])).

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

fof(f715,plain,(
    spl13_2 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | spl13_2 ),
    inference(subsumption_resolution,[],[f713,f61])).

fof(f713,plain,
    ( v2_struct_0(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f712,f62])).

fof(f712,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f711,f63])).

fof(f711,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f710,f69])).

fof(f710,plain,
    ( ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f709,f72])).

fof(f709,plain,
    ( ~ m1_pre_topc(sK10,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_2 ),
    inference(resolution,[],[f708,f686])).

fof(f708,plain,
    ( ~ sP6(sK8,sK10,sK9,sK7,sK12,sK11)
    | spl13_2 ),
    inference(resolution,[],[f129,f117])).

fof(f129,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl13_2
  <=> v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f706,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl13_1 ),
    inference(subsumption_resolution,[],[f704,f61])).

fof(f704,plain,
    ( v2_struct_0(sK7)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f703,f62])).

fof(f703,plain,
    ( ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f702,f63])).

fof(f702,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f701,f69])).

fof(f701,plain,
    ( ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f700,f72])).

fof(f700,plain,
    ( ~ m1_pre_topc(sK10,sK7)
    | ~ m1_pre_topc(sK9,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl13_1 ),
    inference(resolution,[],[f686,f139])).

fof(f139,plain,
    ( ~ sP6(sK8,sK10,sK9,sK7,sK12,sK11)
    | spl13_1 ),
    inference(resolution,[],[f116,f125])).

fof(f125,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl13_1
  <=> v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f303,plain,
    ( ~ spl13_5
    | spl13_6 ),
    inference(avatar_split_clause,[],[f291,f300,f296])).

fof(f291,plain,
    ( sP2(sK12,sK11,sK10,sK9,sK8,sK7)
    | ~ sP3(sK12,sK10,sK9,sK7,sK8,sK11) ),
    inference(resolution,[],[f101,f82])).

fof(f82,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8),k3_tmap_1(sK7,sK8,sK9,k2_tsep_1(sK7,sK9,sK10),sK11),k3_tmap_1(sK7,sK8,sK10,k2_tsep_1(sK7,sK9,sK10),sK12)) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0))
      | sP2(X0,X5,X1,X2,X4,X3)
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( sP2(X0,X5,X1,X2,X4,X3)
          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0)) )
        & ( r2_funct_2(u1_struct_0(k2_tsep_1(X3,X2,X1)),u1_struct_0(X4),k3_tmap_1(X3,X4,X2,k2_tsep_1(X3,X2,X1),X5),k3_tmap_1(X3,X4,X1,k2_tsep_1(X3,X2,X1),X0))
          | ~ sP2(X0,X5,X1,X2,X4,X3) ) )
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X5,X3,X2,X0,X1,X4] :
      ( ( ( sP2(X5,X4,X3,X2,X1,X0)
          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
        & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          | ~ sP2(X5,X4,X3,X2,X1,X0) ) )
      | ~ sP3(X5,X3,X2,X0,X1,X4) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f138,plain,
    ( ~ spl13_1
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f83,f135,f131,f127,f123])).

fof(f83,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))))
    | ~ v5_pre_topc(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),k1_tsep_1(sK7,sK9,sK10),sK8)
    | ~ v1_funct_2(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12),u1_struct_0(k1_tsep_1(sK7,sK9,sK10)),u1_struct_0(sK8))
    | ~ v1_funct_1(k10_tmap_1(sK7,sK8,sK9,sK10,sK11,sK12)) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------

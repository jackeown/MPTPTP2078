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
% DateTime   : Thu Dec  3 13:19:53 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  251 (1554 expanded)
%              Number of leaves         :   32 ( 780 expanded)
%              Depth                    :   24
%              Number of atoms          : 1776 (38886 expanded)
%              Number of equality atoms :   42 (1754 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f145,f174,f278,f326,f462,f471,f643,f665,f672,f674,f688,f842,f853,f857])).

fof(f857,plain,
    ( spl11_4
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f856])).

fof(f856,plain,
    ( $false
    | spl11_4
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f854,f662])).

fof(f662,plain,
    ( sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl11_15
  <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f854,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_4 ),
    inference(resolution,[],[f125,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f106,f73])).

fof(f73,plain,(
    sK5 = k1_tsep_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
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
    & v1_tsep_1(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & v1_tsep_1(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f10,f37,f36,f35,f34,f33,f32])).

fof(f32,plain,
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
                  & v1_tsep_1(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & v1_tsep_1(X2,sK5)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
                & v1_tsep_1(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
            & v1_tsep_1(X2,sK5)
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
              & v1_tsep_1(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
          & v1_tsep_1(X2,sK5)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
            & v1_tsep_1(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & v1_tsep_1(X2,sK5)
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
          & v1_tsep_1(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & v1_tsep_1(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
        & v1_tsep_1(X3,sK5)
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
      & v1_tsep_1(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP4(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP4(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f125,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_4
  <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f853,plain,
    ( spl11_3
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f849,f661,f460,f265,f119])).

fof(f119,plain,
    ( spl11_3
  <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f265,plain,
    ( spl11_8
  <=> sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f460,plain,
    ( spl11_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
        | sP0(X1,sK8,sK7,sK5,X0)
        | ~ sP1(X1,sK8,X0,sK7,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f849,plain,
    ( v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_15 ),
    inference(resolution,[],[f847,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,sK8,sK7,sK5,X0)
      | v5_pre_topc(X0,sK5,X1) ) ),
    inference(superposition,[],[f88,f73])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f847,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f846,f662])).

fof(f846,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f845,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f845,plain,
    ( sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f844,f58])).

fof(f58,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f844,plain,
    ( ~ l1_pre_topc(sK6)
    | sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f843,f57])).

fof(f57,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f843,plain,
    ( ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | v2_struct_0(sK6)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_8
    | ~ spl11_14 ),
    inference(resolution,[],[f266,f478])).

fof(f478,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
        | v2_struct_0(X0)
        | ~ sP4(X0,sK8,sK7,sK5,X2,X1) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f477,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
      | ~ sP4(X0,sK8,sK7,sK5,X2,X1) ) ),
    inference(superposition,[],[f105,f73])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f477,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
        | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
        | ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
        | ~ sP4(X0,sK8,sK7,sK5,X2,X1) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f472,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP4(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f472,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
        | ~ v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0))
        | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2))
        | ~ sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5)
        | ~ sP4(X0,sK8,sK7,sK5,X2,X1) )
    | ~ spl11_14 ),
    inference(resolution,[],[f461,f196])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
        | sP0(X1,sK8,sK7,sK5,X0)
        | ~ sP1(X1,sK8,X0,sK7,sK5) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f460])).

fof(f266,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f265])).

fof(f842,plain,
    ( spl11_8
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f841,f323,f269,f265])).

fof(f269,plain,
    ( spl11_9
  <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f323,plain,
    ( spl11_12
  <=> sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f841,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f840,f65])).

fof(f65,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f38])).

fof(f840,plain,
    ( ~ v1_funct_1(sK9)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f839,f271])).

fof(f271,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f269])).

fof(f839,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f838,f66])).

fof(f66,plain,(
    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f38])).

fof(f838,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f837,f271])).

fof(f837,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f836,f67])).

fof(f67,plain,(
    v5_pre_topc(sK9,sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f836,plain,
    ( ~ v5_pre_topc(sK9,sK7,sK6)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f835,f271])).

fof(f835,plain,
    ( sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f834,f68])).

fof(f68,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f834,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f823,f271])).

fof(f823,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f822,f69])).

fof(f69,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f38])).

fof(f822,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f821,f70])).

fof(f70,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f38])).

fof(f821,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f820,f71])).

fof(f71,plain,(
    v5_pre_topc(sK10,sK8,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f820,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v5_pre_topc(sK10,sK8,sK6)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f817,f72])).

fof(f72,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f817,plain,
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
    inference(superposition,[],[f583,f325])).

fof(f325,plain,
    ( sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f323])).

fof(f583,plain,(
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
    inference(superposition,[],[f85,f73])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f688,plain,
    ( spl11_2
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | spl11_2
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f686,f662])).

fof(f686,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_2 ),
    inference(resolution,[],[f117,f194])).

fof(f117,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl11_2
  <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f674,plain,
    ( ~ spl11_7
    | spl11_10
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | ~ spl11_7
    | spl11_10
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f659,f662])).

fof(f659,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f658,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f658,plain,
    ( v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f657,f54])).

fof(f54,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f657,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f656,f55])).

fof(f55,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f656,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f655,f56])).

fof(f655,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f654,f57])).

fof(f654,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f653,f58])).

fof(f653,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_10 ),
    inference(subsumption_resolution,[],[f652,f144])).

fof(f144,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_7
  <=> m1_pre_topc(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f652,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_10 ),
    inference(subsumption_resolution,[],[f432,f61])).

fof(f61,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f432,plain,
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
    inference(resolution,[],[f343,f277])).

fof(f277,plain,
    ( ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl11_10
  <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f343,plain,(
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
    inference(subsumption_resolution,[],[f342,f104])).

fof(f342,plain,(
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
    inference(subsumption_resolution,[],[f329,f194])).

fof(f329,plain,(
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
    inference(resolution,[],[f103,f196])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(definition_folding,[],[f20,f28])).

fof(f28,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP3(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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

fof(f672,plain,(
    spl11_15 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | spl11_15 ),
    inference(subsumption_resolution,[],[f670,f53])).

fof(f670,plain,
    ( v2_struct_0(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f669,f54])).

fof(f669,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f668,f55])).

fof(f668,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f667,f61])).

fof(f667,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f666,f64])).

fof(f64,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f666,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_15 ),
    inference(resolution,[],[f663,f610])).

fof(f610,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f609,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f609,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f608,f65])).

fof(f608,plain,(
    ! [X0] :
      ( sP4(sK6,sK8,sK7,X0,sK10,sK9)
      | ~ v1_funct_1(sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ m1_pre_topc(sK7,X0)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f595,f66])).

fof(f595,plain,(
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
    inference(resolution,[],[f536,f68])).

fof(f536,plain,(
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
    inference(subsumption_resolution,[],[f535,f56])).

fof(f535,plain,(
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
    inference(subsumption_resolution,[],[f534,f57])).

fof(f534,plain,(
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
    inference(subsumption_resolution,[],[f533,f58])).

fof(f533,plain,(
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
    inference(subsumption_resolution,[],[f532,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f532,plain,(
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
    inference(subsumption_resolution,[],[f531,f69])).

fof(f531,plain,(
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
    inference(subsumption_resolution,[],[f502,f70])).

fof(f502,plain,(
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
    inference(resolution,[],[f107,f72])).

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(definition_folding,[],[f22,f30])).

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

fof(f663,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f661])).

fof(f665,plain,
    ( ~ spl11_15
    | ~ spl11_7
    | spl11_11 ),
    inference(avatar_split_clause,[],[f651,f319,f142,f661])).

fof(f319,plain,
    ( spl11_11
  <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f651,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f650,f53])).

fof(f650,plain,
    ( v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f649,f54])).

fof(f649,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f648,f55])).

fof(f648,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f647,f56])).

fof(f647,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f646,f57])).

fof(f646,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f645,f58])).

fof(f645,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | ~ spl11_7
    | spl11_11 ),
    inference(subsumption_resolution,[],[f644,f144])).

fof(f644,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_11 ),
    inference(subsumption_resolution,[],[f433,f64])).

fof(f433,plain,
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
    inference(resolution,[],[f343,f321])).

fof(f321,plain,
    ( ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f319])).

fof(f643,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f641,f53])).

fof(f641,plain,
    ( v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f640,f54])).

fof(f640,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f639,f55])).

fof(f639,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f638,f61])).

fof(f638,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f637,f64])).

fof(f637,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_1 ),
    inference(resolution,[],[f610,f148])).

fof(f148,plain,
    ( ~ sP4(sK6,sK8,sK7,sK5,sK10,sK9)
    | spl11_1 ),
    inference(resolution,[],[f104,f113])).

fof(f113,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl11_1
  <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f471,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | spl11_13 ),
    inference(subsumption_resolution,[],[f469,f53])).

fof(f469,plain,
    ( v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f468,f54])).

fof(f468,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f467,f55])).

fof(f467,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f466,f60])).

fof(f60,plain,(
    v1_tsep_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f466,plain,
    ( ~ v1_tsep_1(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f465,f61])).

fof(f465,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ v1_tsep_1(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f464,f63])).

fof(f63,plain,(
    v1_tsep_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f464,plain,
    ( ~ v1_tsep_1(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_tsep_1(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f463,f64])).

fof(f463,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | ~ v1_tsep_1(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_tsep_1(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_13 ),
    inference(resolution,[],[f458,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f458,plain,
    ( ~ r4_tsep_1(sK5,sK7,sK8)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl11_13
  <=> r4_tsep_1(sK5,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f462,plain,
    ( ~ spl11_13
    | spl11_14 ),
    inference(avatar_split_clause,[],[f454,f460,f456])).

fof(f454,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f453,f53])).

fof(f453,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f452,f54])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f451,f55])).

fof(f451,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f450,f59])).

fof(f450,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f449,f61])).

fof(f449,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f448,f62])).

fof(f448,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
      | ~ sP1(X1,sK8,X0,sK7,sK5)
      | sP0(X1,sK8,sK7,sK5,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK5,sK7,sK8)
      | v2_struct_0(sK8)
      | ~ m1_pre_topc(sK7,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f439,f64])).

fof(f439,plain,(
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
    inference(superposition,[],[f92,f73])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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

fof(f326,plain,
    ( ~ spl11_11
    | spl11_12 ),
    inference(avatar_split_clause,[],[f317,f323,f319])).

fof(f317,plain,
    ( sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    inference(resolution,[],[f258,f128])).

fof(f128,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(forward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) ),
    inference(cnf_transformation,[],[f38])).

fof(f258,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f257,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP3(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f257,plain,(
    ! [X2,X3,X1] :
      ( sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3))
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f252,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f252,plain,(
    ! [X2,X3,X1] :
      ( sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3)
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10)
      | ~ v1_funct_2(k3_tmap_1(X1,sK6,X2,sK8,X3),u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3))
      | ~ sP3(sK6,sK8,X3,X2,X1) ) ),
    inference(resolution,[],[f236,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP3(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f236,plain,(
    ! [X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | sK10 = X45
      | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f235,f69])).

fof(f235,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | sK10 = X45
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(subsumption_resolution,[],[f214,f70])).

fof(f214,plain,(
    ! [X45] :
      ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10)
      | sK10 = X45
      | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(sK10)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(X45) ) ),
    inference(resolution,[],[f98,f72])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f278,plain,
    ( ~ spl11_10
    | spl11_9 ),
    inference(avatar_split_clause,[],[f273,f269,f275])).

fof(f273,plain,
    ( sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))
    | ~ sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) ),
    inference(resolution,[],[f245,f127])).

fof(f127,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f74,plain,(
    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) ),
    inference(cnf_transformation,[],[f38])).

fof(f245,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f244,f100])).

fof(f244,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3))
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f239,f101])).

fof(f239,plain,(
    ! [X2,X3,X1] :
      ( sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3)
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9)
      | ~ v1_funct_2(k3_tmap_1(X1,sK6,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3))
      | ~ sP3(sK6,sK7,X3,X2,X1) ) ),
    inference(resolution,[],[f234,f102])).

fof(f234,plain,(
    ! [X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | sK9 = X44
      | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f233,f65])).

fof(f233,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | sK9 = X44
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(subsumption_resolution,[],[f213,f66])).

fof(f213,plain,(
    ! [X44] :
      ( ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9)
      | sK9 = X44
      | ~ v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(X44) ) ),
    inference(resolution,[],[f98,f68])).

fof(f174,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl11_5 ),
    inference(subsumption_resolution,[],[f172,f53])).

fof(f172,plain,
    ( v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f171,f55])).

fof(f171,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f170,f59])).

fof(f170,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f169,f61])).

fof(f169,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f168,f62])).

fof(f168,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f167,f64])).

fof(f167,plain,
    ( ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl11_5 ),
    inference(resolution,[],[f97,f134])).

fof(f134,plain,
    ( ~ sP2(sK5,sK8,sK7)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl11_5
  <=> sP2(sK5,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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

fof(f145,plain,
    ( ~ spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f140,f142,f132])).

fof(f140,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ sP2(sK5,sK8,sK7) ),
    inference(superposition,[],[f96,f73])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f126,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f76,f123,f119,f115,f111])).

fof(f76,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)
    | ~ v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (12794)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (12810)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (12792)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (12793)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (12818)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (12801)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (12799)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (12808)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (12811)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (12795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (12814)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (12797)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (12816)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (12802)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (12812)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (12796)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (12803)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (12805)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12815)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (12807)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (12809)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (12813)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (12800)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (12798)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (12817)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (12804)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.67/0.60  % (12796)Refutation found. Thanks to Tanya!
% 1.67/0.60  % SZS status Theorem for theBenchmark
% 1.67/0.60  % SZS output start Proof for theBenchmark
% 1.67/0.60  fof(f860,plain,(
% 1.67/0.60    $false),
% 1.67/0.60    inference(avatar_sat_refutation,[],[f126,f145,f174,f278,f326,f462,f471,f643,f665,f672,f674,f688,f842,f853,f857])).
% 1.67/0.60  fof(f857,plain,(
% 1.67/0.60    spl11_4 | ~spl11_15),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f856])).
% 1.67/0.60  fof(f856,plain,(
% 1.67/0.60    $false | (spl11_4 | ~spl11_15)),
% 1.67/0.60    inference(subsumption_resolution,[],[f854,f662])).
% 1.67/0.60  fof(f662,plain,(
% 1.67/0.60    sP4(sK6,sK8,sK7,sK5,sK10,sK9) | ~spl11_15),
% 1.67/0.60    inference(avatar_component_clause,[],[f661])).
% 1.67/0.60  fof(f661,plain,(
% 1.67/0.60    spl11_15 <=> sP4(sK6,sK8,sK7,sK5,sK10,sK9)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 1.67/0.60  fof(f854,plain,(
% 1.67/0.60    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_4),
% 1.67/0.60    inference(resolution,[],[f125,f196])).
% 1.67/0.60  fof(f196,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.67/0.60    inference(superposition,[],[f106,f73])).
% 1.67/0.60  fof(f73,plain,(
% 1.67/0.60    sK5 = k1_tsep_1(sK5,sK7,sK8)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f38,plain,(
% 1.67/0.60    ((((((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(sK10,sK8,sK6) & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(sK9,sK7,sK6) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(sK9)) & m1_pre_topc(sK8,sK5) & v1_tsep_1(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & v1_tsep_1(sK7,sK5) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 1.67/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f10,f37,f36,f35,f34,f33,f32])).
% 1.67/0.60  fof(f32,plain,(
% 1.67/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1) | ~v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_tsep_1(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f33,plain,(
% 1.67/0.60    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK5,X1,X2,X3,X4,X5),sK5,X1) | ~v1_funct_2(k10_tmap_1(sK5,X1,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK5,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,X1,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_tsep_1(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6)))) & v5_pre_topc(X4,X2,sK6) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_tsep_1(X2,sK5) & ~v2_struct_0(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f34,plain,(
% 1.67/0.60    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,X2,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X3,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,X2,X3),X2,k10_tmap_1(sK5,sK6,X2,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6)))) & v5_pre_topc(X4,X2,sK6) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & v1_tsep_1(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & v1_tsep_1(sK7,sK5) & ~v2_struct_0(sK7))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f35,plain,(
% 1.67/0.60    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),X3,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,X3),sK7,k10_tmap_1(sK5,sK6,sK7,X3,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6)))) & v5_pre_topc(X5,X3,sK6) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) & m1_pre_topc(sK8,sK5) & v1_tsep_1(sK8,sK5) & ~v2_struct_0(sK8))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f36,plain,(
% 1.67/0.60    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,X4,X5)),X4) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(X4,sK7,sK6) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) & v5_pre_topc(sK9,sK7,sK6) & v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) & v1_funct_1(sK9))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f37,plain,(
% 1.67/0.60    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),X5) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,X5)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(X5,sK8,sK6) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) & r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10) & r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9) & sK5 = k1_tsep_1(sK5,sK7,sK8) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) & v5_pre_topc(sK10,sK8,sK6) & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) & v1_funct_1(sK10))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f10,plain,(
% 1.67/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.67/0.60    inference(flattening,[],[f9])).
% 1.67/0.60  fof(f9,plain,(
% 1.67/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.67/0.60    inference(ennf_transformation,[],[f8])).
% 1.67/0.60  fof(f8,negated_conjecture,(
% 1.67/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.67/0.60    inference(negated_conjecture,[],[f7])).
% 1.67/0.60  fof(f7,conjecture,(
% 1.67/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_tmap_1)).
% 1.67/0.60  fof(f106,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f52])).
% 1.67/0.60  fof(f52,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP4(X0,X1,X2,X3,X4,X5))),
% 1.67/0.60    inference(rectify,[],[f51])).
% 1.67/0.60  fof(f51,plain,(
% 1.67/0.60    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP4(X1,X3,X2,X0,X5,X4))),
% 1.67/0.60    inference(nnf_transformation,[],[f30])).
% 1.67/0.60  fof(f30,plain,(
% 1.67/0.60    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP4(X1,X3,X2,X0,X5,X4))),
% 1.67/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.67/0.60  fof(f125,plain,(
% 1.67/0.60    ~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | spl11_4),
% 1.67/0.60    inference(avatar_component_clause,[],[f123])).
% 1.67/0.60  fof(f123,plain,(
% 1.67/0.60    spl11_4 <=> m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.67/0.60  fof(f853,plain,(
% 1.67/0.60    spl11_3 | ~spl11_8 | ~spl11_14 | ~spl11_15),
% 1.67/0.60    inference(avatar_split_clause,[],[f849,f661,f460,f265,f119])).
% 1.67/0.60  fof(f119,plain,(
% 1.67/0.60    spl11_3 <=> v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.67/0.60  fof(f265,plain,(
% 1.67/0.60    spl11_8 <=> sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.67/0.60  fof(f460,plain,(
% 1.67/0.60    spl11_14 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | sP0(X1,sK8,sK7,sK5,X0) | ~sP1(X1,sK8,X0,sK7,sK5))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.67/0.60  fof(f849,plain,(
% 1.67/0.60    v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | (~spl11_8 | ~spl11_14 | ~spl11_15)),
% 1.67/0.60    inference(resolution,[],[f847,f146])).
% 1.67/0.60  fof(f146,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~sP0(X1,sK8,sK7,sK5,X0) | v5_pre_topc(X0,sK5,X1)) )),
% 1.67/0.60    inference(superposition,[],[f88,f73])).
% 1.67/0.60  fof(f88,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f44])).
% 1.67/0.60  fof(f44,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.67/0.60    inference(rectify,[],[f43])).
% 1.67/0.60  fof(f43,plain,(
% 1.67/0.60    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.67/0.60    inference(flattening,[],[f42])).
% 1.67/0.60  fof(f42,plain,(
% 1.67/0.60    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 1.67/0.60    inference(nnf_transformation,[],[f23])).
% 1.67/0.60  fof(f23,plain,(
% 1.67/0.60    ! [X1,X3,X2,X0,X4] : (sP0(X1,X3,X2,X0,X4) <=> (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))),
% 1.67/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.67/0.60  fof(f847,plain,(
% 1.67/0.60    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | (~spl11_8 | ~spl11_14 | ~spl11_15)),
% 1.67/0.60    inference(subsumption_resolution,[],[f846,f662])).
% 1.67/0.60  fof(f846,plain,(
% 1.67/0.60    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_8 | ~spl11_14)),
% 1.67/0.60    inference(subsumption_resolution,[],[f845,f56])).
% 1.67/0.60  fof(f56,plain,(
% 1.67/0.60    ~v2_struct_0(sK6)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f845,plain,(
% 1.67/0.60    sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_8 | ~spl11_14)),
% 1.67/0.60    inference(subsumption_resolution,[],[f844,f58])).
% 1.67/0.60  fof(f58,plain,(
% 1.67/0.60    l1_pre_topc(sK6)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f844,plain,(
% 1.67/0.60    ~l1_pre_topc(sK6) | sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_8 | ~spl11_14)),
% 1.67/0.60    inference(subsumption_resolution,[],[f843,f57])).
% 1.67/0.60  fof(f57,plain,(
% 1.67/0.60    v2_pre_topc(sK6)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f843,plain,(
% 1.67/0.60    ~v2_pre_topc(sK6) | ~l1_pre_topc(sK6) | sP0(sK6,sK8,sK7,sK5,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | v2_struct_0(sK6) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_8 | ~spl11_14)),
% 1.67/0.60    inference(resolution,[],[f266,f478])).
% 1.67/0.60  fof(f478,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | v2_struct_0(X0) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) ) | ~spl11_14),
% 1.67/0.60    inference(subsumption_resolution,[],[f477,f194])).
% 1.67/0.60  fof(f194,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) )),
% 1.67/0.60    inference(superposition,[],[f105,f73])).
% 1.67/0.60  fof(f105,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f52])).
% 1.67/0.60  fof(f477,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) ) | ~spl11_14),
% 1.67/0.60    inference(subsumption_resolution,[],[f472,f104])).
% 1.67/0.60  fof(f104,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP4(X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f52])).
% 1.67/0.60  fof(f472,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~v1_funct_2(k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),u1_struct_0(sK5),u1_struct_0(X0)) | sP0(X0,sK8,sK7,sK5,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2)) | ~sP1(X0,sK8,k10_tmap_1(sK5,X0,sK7,sK8,X1,X2),sK7,sK5) | ~sP4(X0,sK8,sK7,sK5,X2,X1)) ) | ~spl11_14),
% 1.67/0.60    inference(resolution,[],[f461,f196])).
% 1.67/0.60  fof(f461,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | sP0(X1,sK8,sK7,sK5,X0) | ~sP1(X1,sK8,X0,sK7,sK5)) ) | ~spl11_14),
% 1.67/0.60    inference(avatar_component_clause,[],[f460])).
% 1.67/0.60  fof(f266,plain,(
% 1.67/0.60    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~spl11_8),
% 1.67/0.60    inference(avatar_component_clause,[],[f265])).
% 1.67/0.60  fof(f842,plain,(
% 1.67/0.60    spl11_8 | ~spl11_9 | ~spl11_12),
% 1.67/0.60    inference(avatar_split_clause,[],[f841,f323,f269,f265])).
% 1.67/0.60  fof(f269,plain,(
% 1.67/0.60    spl11_9 <=> sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.67/0.60  fof(f323,plain,(
% 1.67/0.60    spl11_12 <=> sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.67/0.60  fof(f841,plain,(
% 1.67/0.60    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(subsumption_resolution,[],[f840,f65])).
% 1.67/0.60  fof(f65,plain,(
% 1.67/0.60    v1_funct_1(sK9)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f840,plain,(
% 1.67/0.60    ~v1_funct_1(sK9) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(forward_demodulation,[],[f839,f271])).
% 1.67/0.60  fof(f271,plain,(
% 1.67/0.60    sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~spl11_9),
% 1.67/0.60    inference(avatar_component_clause,[],[f269])).
% 1.67/0.60  fof(f839,plain,(
% 1.67/0.60    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(subsumption_resolution,[],[f838,f66])).
% 1.67/0.60  fof(f66,plain,(
% 1.67/0.60    v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6))),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f838,plain,(
% 1.67/0.60    ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(forward_demodulation,[],[f837,f271])).
% 1.67/0.60  fof(f837,plain,(
% 1.67/0.60    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(subsumption_resolution,[],[f836,f67])).
% 1.67/0.60  fof(f67,plain,(
% 1.67/0.60    v5_pre_topc(sK9,sK7,sK6)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f836,plain,(
% 1.67/0.60    ~v5_pre_topc(sK9,sK7,sK6) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(forward_demodulation,[],[f835,f271])).
% 1.67/0.60  fof(f835,plain,(
% 1.67/0.60    sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(subsumption_resolution,[],[f834,f68])).
% 1.67/0.60  fof(f68,plain,(
% 1.67/0.60    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f834,plain,(
% 1.67/0.60    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | (~spl11_9 | ~spl11_12)),
% 1.67/0.60    inference(forward_demodulation,[],[f823,f271])).
% 1.67/0.60  fof(f823,plain,(
% 1.67/0.60    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.67/0.60    inference(subsumption_resolution,[],[f822,f69])).
% 1.67/0.60  fof(f69,plain,(
% 1.67/0.60    v1_funct_1(sK10)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f822,plain,(
% 1.67/0.60    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.67/0.60    inference(subsumption_resolution,[],[f821,f70])).
% 1.67/0.60  fof(f70,plain,(
% 1.67/0.60    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6))),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f821,plain,(
% 1.67/0.60    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.67/0.60    inference(subsumption_resolution,[],[f820,f71])).
% 1.67/0.60  fof(f71,plain,(
% 1.67/0.60    v5_pre_topc(sK10,sK8,sK6)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f820,plain,(
% 1.67/0.60    ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v5_pre_topc(sK10,sK8,sK6) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.67/0.60    inference(subsumption_resolution,[],[f817,f72])).
% 1.67/0.60  fof(f72,plain,(
% 1.67/0.60    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f817,plain,(
% 1.67/0.60    ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~m1_subset_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v5_pre_topc(sK10,sK8,sK6) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | sP1(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK7,sK6) | ~v1_funct_2(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))) | ~spl11_12),
% 1.67/0.60    inference(superposition,[],[f583,f325])).
% 1.67/0.60  fof(f325,plain,(
% 1.67/0.60    sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~spl11_12),
% 1.67/0.60    inference(avatar_component_clause,[],[f323])).
% 1.67/0.60  fof(f583,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK8,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK5,X0,sK5,sK7,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK8,X1),sK8,X0) | ~v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK8,X1),u1_struct_0(sK8),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK8,X1)) | sP1(X0,sK8,X1,sK7,sK5) | ~v5_pre_topc(k3_tmap_1(sK5,X0,sK5,sK7,X1),sK7,X0) | ~v1_funct_2(k3_tmap_1(sK5,X0,sK5,sK7,X1),u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK5,X0,sK5,sK7,X1))) )),
% 1.67/0.60    inference(superposition,[],[f85,f73])).
% 1.67/0.60  fof(f85,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP1(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f41])).
% 1.67/0.60  fof(f41,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP1(X0,X1,X2,X3,X4)))),
% 1.67/0.60    inference(rectify,[],[f40])).
% 1.67/0.60  fof(f40,plain,(
% 1.67/0.60    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.67/0.60    inference(flattening,[],[f39])).
% 1.67/0.60  fof(f39,plain,(
% 1.67/0.60    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 1.67/0.60    inference(nnf_transformation,[],[f24])).
% 1.67/0.60  fof(f24,plain,(
% 1.67/0.60    ! [X1,X3,X4,X2,X0] : (sP1(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 1.67/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.67/0.60  fof(f688,plain,(
% 1.67/0.60    spl11_2 | ~spl11_15),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f687])).
% 1.67/0.60  fof(f687,plain,(
% 1.67/0.60    $false | (spl11_2 | ~spl11_15)),
% 1.67/0.60    inference(subsumption_resolution,[],[f686,f662])).
% 1.67/0.60  fof(f686,plain,(
% 1.67/0.60    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_2),
% 1.67/0.60    inference(resolution,[],[f117,f194])).
% 1.67/0.60  fof(f117,plain,(
% 1.67/0.60    ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | spl11_2),
% 1.67/0.60    inference(avatar_component_clause,[],[f115])).
% 1.67/0.60  fof(f115,plain,(
% 1.67/0.60    spl11_2 <=> v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.67/0.60  fof(f674,plain,(
% 1.67/0.60    ~spl11_7 | spl11_10 | ~spl11_15),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f673])).
% 1.67/0.60  fof(f673,plain,(
% 1.67/0.60    $false | (~spl11_7 | spl11_10 | ~spl11_15)),
% 1.67/0.60    inference(subsumption_resolution,[],[f659,f662])).
% 1.67/0.60  fof(f659,plain,(
% 1.67/0.60    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f658,f53])).
% 1.67/0.60  fof(f53,plain,(
% 1.67/0.60    ~v2_struct_0(sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f658,plain,(
% 1.67/0.60    v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f657,f54])).
% 1.67/0.60  fof(f54,plain,(
% 1.67/0.60    v2_pre_topc(sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f657,plain,(
% 1.67/0.60    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f656,f55])).
% 1.67/0.60  fof(f55,plain,(
% 1.67/0.60    l1_pre_topc(sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f656,plain,(
% 1.67/0.60    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f655,f56])).
% 1.67/0.60  fof(f655,plain,(
% 1.67/0.60    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f654,f57])).
% 1.67/0.60  fof(f654,plain,(
% 1.67/0.60    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f653,f58])).
% 1.67/0.60  fof(f653,plain,(
% 1.67/0.60    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_10)),
% 1.67/0.60    inference(subsumption_resolution,[],[f652,f144])).
% 1.67/0.60  fof(f144,plain,(
% 1.67/0.60    m1_pre_topc(sK5,sK5) | ~spl11_7),
% 1.67/0.60    inference(avatar_component_clause,[],[f142])).
% 1.67/0.60  fof(f142,plain,(
% 1.67/0.60    spl11_7 <=> m1_pre_topc(sK5,sK5)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.67/0.60  fof(f652,plain,(
% 1.67/0.60    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_10),
% 1.67/0.60    inference(subsumption_resolution,[],[f432,f61])).
% 1.67/0.60  fof(f61,plain,(
% 1.67/0.60    m1_pre_topc(sK7,sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f432,plain,(
% 1.67/0.60    ~m1_pre_topc(sK7,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_10),
% 1.67/0.60    inference(resolution,[],[f343,f277])).
% 1.67/0.60  fof(f277,plain,(
% 1.67/0.60    ~sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) | spl11_10),
% 1.67/0.60    inference(avatar_component_clause,[],[f275])).
% 1.67/0.60  fof(f275,plain,(
% 1.67/0.60    spl11_10 <=> sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.67/0.60  fof(f343,plain,(
% 1.67/0.60    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f342,f104])).
% 1.67/0.60  fof(f342,plain,(
% 1.67/0.60    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f329,f194])).
% 1.67/0.60  fof(f329,plain,(
% 1.67/0.60    ( ! [X12,X10,X8,X11,X9] : (sP3(X8,X9,k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),sK5,X12) | ~v1_funct_2(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11),u1_struct_0(sK5),u1_struct_0(X8)) | ~v1_funct_1(k10_tmap_1(sK5,X8,sK7,sK8,X10,X11)) | ~m1_pre_topc(X9,X12) | ~m1_pre_topc(sK5,X12) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~sP4(X8,sK8,sK7,sK5,X11,X10)) )),
% 1.67/0.60    inference(resolution,[],[f103,f196])).
% 1.67/0.60  fof(f103,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP3(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f29])).
% 1.67/0.60  fof(f29,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : (sP3(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(definition_folding,[],[f20,f28])).
% 1.67/0.60  fof(f28,plain,(
% 1.67/0.60    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP3(X1,X3,X4,X2,X0))),
% 1.67/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.67/0.60  fof(f20,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(flattening,[],[f19])).
% 1.67/0.60  fof(f19,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.60    inference(ennf_transformation,[],[f4])).
% 1.67/0.60  fof(f4,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.67/0.60  fof(f672,plain,(
% 1.67/0.60    spl11_15),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f671])).
% 1.67/0.60  fof(f671,plain,(
% 1.67/0.60    $false | spl11_15),
% 1.67/0.60    inference(subsumption_resolution,[],[f670,f53])).
% 1.67/0.60  fof(f670,plain,(
% 1.67/0.60    v2_struct_0(sK5) | spl11_15),
% 1.67/0.60    inference(subsumption_resolution,[],[f669,f54])).
% 1.67/0.60  fof(f669,plain,(
% 1.67/0.60    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_15),
% 1.67/0.60    inference(subsumption_resolution,[],[f668,f55])).
% 1.67/0.60  fof(f668,plain,(
% 1.67/0.60    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_15),
% 1.67/0.60    inference(subsumption_resolution,[],[f667,f61])).
% 1.67/0.60  fof(f667,plain,(
% 1.67/0.60    ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_15),
% 1.67/0.60    inference(subsumption_resolution,[],[f666,f64])).
% 1.67/0.60  fof(f64,plain,(
% 1.67/0.60    m1_pre_topc(sK8,sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f666,plain,(
% 1.67/0.60    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_15),
% 1.67/0.60    inference(resolution,[],[f663,f610])).
% 1.67/0.60  fof(f610,plain,(
% 1.67/0.60    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f609,f59])).
% 1.67/0.60  fof(f59,plain,(
% 1.67/0.60    ~v2_struct_0(sK7)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f609,plain,(
% 1.67/0.60    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f608,f65])).
% 1.67/0.60  fof(f608,plain,(
% 1.67/0.60    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~v1_funct_1(sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f595,f66])).
% 1.67/0.60  fof(f595,plain,(
% 1.67/0.60    ( ! [X0] : (sP4(sK6,sK8,sK7,X0,sK10,sK9) | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(sK9) | ~m1_pre_topc(sK8,X0) | ~m1_pre_topc(sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(resolution,[],[f536,f68])).
% 1.67/0.60  fof(f536,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f535,f56])).
% 1.67/0.60  fof(f535,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f534,f57])).
% 1.67/0.60  fof(f534,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f533,f58])).
% 1.67/0.60  fof(f533,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f532,f62])).
% 1.67/0.60  fof(f62,plain,(
% 1.67/0.60    ~v2_struct_0(sK8)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f532,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f531,f69])).
% 1.67/0.60  fof(f531,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_1(sK10) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f502,f70])).
% 1.67/0.60  fof(f502,plain,(
% 1.67/0.60    ( ! [X66,X67,X65] : (sP4(sK6,sK8,X65,X66,sK10,X67) | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | ~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(sK6)))) | ~v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(sK6)) | ~v1_funct_1(X67) | ~m1_pre_topc(sK8,X66) | v2_struct_0(sK8) | ~m1_pre_topc(X65,X66) | v2_struct_0(X65) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(X66) | ~v2_pre_topc(X66) | v2_struct_0(X66)) )),
% 1.67/0.60    inference(resolution,[],[f107,f72])).
% 1.67/0.60  fof(f107,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP4(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f31])).
% 1.67/0.60  fof(f31,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5] : (sP4(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(definition_folding,[],[f22,f30])).
% 1.67/0.60  fof(f22,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(flattening,[],[f21])).
% 1.67/0.60  fof(f21,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.60    inference(ennf_transformation,[],[f2])).
% 1.67/0.60  fof(f2,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.67/0.60  fof(f663,plain,(
% 1.67/0.60    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_15),
% 1.67/0.60    inference(avatar_component_clause,[],[f661])).
% 1.67/0.60  fof(f665,plain,(
% 1.67/0.60    ~spl11_15 | ~spl11_7 | spl11_11),
% 1.67/0.60    inference(avatar_split_clause,[],[f651,f319,f142,f661])).
% 1.67/0.60  fof(f319,plain,(
% 1.67/0.60    spl11_11 <=> sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.67/0.60  fof(f651,plain,(
% 1.67/0.60    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f650,f53])).
% 1.67/0.60  fof(f650,plain,(
% 1.67/0.60    v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f649,f54])).
% 1.67/0.60  fof(f649,plain,(
% 1.67/0.60    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f648,f55])).
% 1.67/0.60  fof(f648,plain,(
% 1.67/0.60    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f647,f56])).
% 1.67/0.60  fof(f647,plain,(
% 1.67/0.60    v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f646,f57])).
% 1.67/0.60  fof(f646,plain,(
% 1.67/0.60    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f645,f58])).
% 1.67/0.60  fof(f645,plain,(
% 1.67/0.60    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | (~spl11_7 | spl11_11)),
% 1.67/0.60    inference(subsumption_resolution,[],[f644,f144])).
% 1.67/0.60  fof(f644,plain,(
% 1.67/0.60    ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_11),
% 1.67/0.60    inference(subsumption_resolution,[],[f433,f64])).
% 1.67/0.60  fof(f433,plain,(
% 1.67/0.60    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK5,sK5) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_11),
% 1.67/0.60    inference(resolution,[],[f343,f321])).
% 1.67/0.60  fof(f321,plain,(
% 1.67/0.60    ~sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5) | spl11_11),
% 1.67/0.60    inference(avatar_component_clause,[],[f319])).
% 1.67/0.60  fof(f643,plain,(
% 1.67/0.60    spl11_1),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f642])).
% 1.67/0.60  fof(f642,plain,(
% 1.67/0.60    $false | spl11_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f641,f53])).
% 1.67/0.60  fof(f641,plain,(
% 1.67/0.60    v2_struct_0(sK5) | spl11_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f640,f54])).
% 1.67/0.60  fof(f640,plain,(
% 1.67/0.60    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f639,f55])).
% 1.67/0.60  fof(f639,plain,(
% 1.67/0.60    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f638,f61])).
% 1.67/0.60  fof(f638,plain,(
% 1.67/0.60    ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f637,f64])).
% 1.67/0.60  fof(f637,plain,(
% 1.67/0.60    ~m1_pre_topc(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_1),
% 1.67/0.60    inference(resolution,[],[f610,f148])).
% 1.67/0.60  fof(f148,plain,(
% 1.67/0.60    ~sP4(sK6,sK8,sK7,sK5,sK10,sK9) | spl11_1),
% 1.67/0.60    inference(resolution,[],[f104,f113])).
% 1.67/0.60  fof(f113,plain,(
% 1.67/0.60    ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | spl11_1),
% 1.67/0.60    inference(avatar_component_clause,[],[f111])).
% 1.67/0.60  fof(f111,plain,(
% 1.67/0.60    spl11_1 <=> v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.67/0.60  fof(f471,plain,(
% 1.67/0.60    spl11_13),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f470])).
% 1.67/0.60  fof(f470,plain,(
% 1.67/0.60    $false | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f469,f53])).
% 1.67/0.60  fof(f469,plain,(
% 1.67/0.60    v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f468,f54])).
% 1.67/0.60  fof(f468,plain,(
% 1.67/0.60    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f467,f55])).
% 1.67/0.60  fof(f467,plain,(
% 1.67/0.60    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f466,f60])).
% 1.67/0.60  fof(f60,plain,(
% 1.67/0.60    v1_tsep_1(sK7,sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f466,plain,(
% 1.67/0.60    ~v1_tsep_1(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f465,f61])).
% 1.67/0.60  fof(f465,plain,(
% 1.67/0.60    ~m1_pre_topc(sK7,sK5) | ~v1_tsep_1(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f464,f63])).
% 1.67/0.60  fof(f63,plain,(
% 1.67/0.60    v1_tsep_1(sK8,sK5)),
% 1.67/0.60    inference(cnf_transformation,[],[f38])).
% 1.67/0.60  fof(f464,plain,(
% 1.67/0.60    ~v1_tsep_1(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~v1_tsep_1(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(subsumption_resolution,[],[f463,f64])).
% 1.67/0.60  fof(f463,plain,(
% 1.67/0.60    ~m1_pre_topc(sK8,sK5) | ~v1_tsep_1(sK8,sK5) | ~m1_pre_topc(sK7,sK5) | ~v1_tsep_1(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | spl11_13),
% 1.67/0.60    inference(resolution,[],[f458,f93])).
% 1.67/0.60  fof(f93,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f14])).
% 1.67/0.60  fof(f14,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(flattening,[],[f13])).
% 1.67/0.60  fof(f13,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.60    inference(ennf_transformation,[],[f6])).
% 1.67/0.60  fof(f6,axiom,(
% 1.67/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).
% 1.67/0.60  fof(f458,plain,(
% 1.67/0.60    ~r4_tsep_1(sK5,sK7,sK8) | spl11_13),
% 1.67/0.60    inference(avatar_component_clause,[],[f456])).
% 1.67/0.60  fof(f456,plain,(
% 1.67/0.60    spl11_13 <=> r4_tsep_1(sK5,sK7,sK8)),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.67/0.60  fof(f462,plain,(
% 1.67/0.60    ~spl11_13 | spl11_14),
% 1.67/0.60    inference(avatar_split_clause,[],[f454,f460,f456])).
% 1.67/0.60  fof(f454,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f453,f53])).
% 1.67/0.60  fof(f453,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f452,f54])).
% 1.67/0.60  fof(f452,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f451,f55])).
% 1.67/0.60  fof(f451,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f450,f59])).
% 1.67/0.60  fof(f450,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f449,f61])).
% 1.67/0.60  fof(f449,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f448,f62])).
% 1.67/0.60  fof(f448,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f439,f64])).
% 1.67/0.60  fof(f439,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~sP1(X1,sK8,X0,sK7,sK5) | sP0(X1,sK8,sK7,sK5,X0) | ~v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK5,sK7,sK8) | ~m1_pre_topc(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 1.67/0.60    inference(superposition,[],[f92,f73])).
% 1.67/0.60  fof(f92,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~sP1(X1,X3,X4,X2,X0) | sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f45])).
% 1.67/0.60  fof(f45,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((sP0(X1,X3,X2,X0,X4) | ~sP1(X1,X3,X4,X2,X0)) & (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(nnf_transformation,[],[f25])).
% 1.67/0.60  fof(f25,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((sP0(X1,X3,X2,X0,X4) <=> sP1(X1,X3,X4,X2,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.60    inference(definition_folding,[],[f12,f24,f23])).
% 1.67/0.61  fof(f12,plain,(
% 1.67/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.61    inference(flattening,[],[f11])).
% 1.67/0.61  fof(f11,plain,(
% 1.67/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.61    inference(ennf_transformation,[],[f5])).
% 1.67/0.61  fof(f5,axiom,(
% 1.67/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 1.67/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 1.67/0.61  fof(f326,plain,(
% 1.67/0.61    ~spl11_11 | spl11_12),
% 1.67/0.61    inference(avatar_split_clause,[],[f317,f323,f319])).
% 1.67/0.61  fof(f317,plain,(
% 1.67/0.61    sK10 = k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP3(sK6,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.67/0.61    inference(resolution,[],[f258,f128])).
% 1.67/0.61  fof(f128,plain,(
% 1.67/0.61    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)),
% 1.67/0.61    inference(forward_demodulation,[],[f75,f73])).
% 1.67/0.61  fof(f75,plain,(
% 1.67/0.61    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK10)),
% 1.67/0.61    inference(cnf_transformation,[],[f38])).
% 1.67/0.61  fof(f258,plain,(
% 1.67/0.61    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f257,f100])).
% 1.67/0.61  fof(f100,plain,(
% 1.67/0.61    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f50])).
% 1.67/0.61  fof(f50,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP3(X0,X1,X2,X3,X4))),
% 1.67/0.61    inference(rectify,[],[f49])).
% 1.67/0.61  fof(f49,plain,(
% 1.67/0.61    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP3(X1,X3,X4,X2,X0))),
% 1.67/0.61    inference(nnf_transformation,[],[f28])).
% 1.67/0.61  fof(f257,plain,(
% 1.67/0.61    ( ! [X2,X3,X1] : (sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3)) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f252,f101])).
% 1.67/0.61  fof(f101,plain,(
% 1.67/0.61    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f50])).
% 1.67/0.61  fof(f252,plain,(
% 1.67/0.61    ( ! [X2,X3,X1] : (sK10 = k3_tmap_1(X1,sK6,X2,sK8,X3) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK8,X3),sK10) | ~v1_funct_2(k3_tmap_1(X1,sK6,X2,sK8,X3),u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK8,X3)) | ~sP3(sK6,sK8,X3,X2,X1)) )),
% 1.67/0.61    inference(resolution,[],[f236,f102])).
% 1.67/0.61  fof(f102,plain,(
% 1.67/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP3(X0,X1,X2,X3,X4)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f50])).
% 1.67/0.61  fof(f236,plain,(
% 1.67/0.61    ( ! [X45] : (~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | sK10 = X45 | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f235,f69])).
% 1.67/0.61  fof(f235,plain,(
% 1.67/0.61    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | sK10 = X45 | ~v1_funct_1(sK10) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f214,f70])).
% 1.67/0.61  fof(f214,plain,(
% 1.67/0.61    ( ! [X45] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK6),X45,sK10) | sK10 = X45 | ~v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(sK10) | ~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) | ~v1_funct_2(X45,u1_struct_0(sK8),u1_struct_0(sK6)) | ~v1_funct_1(X45)) )),
% 1.67/0.61    inference(resolution,[],[f98,f72])).
% 1.67/0.61  fof(f98,plain,(
% 1.67/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f48])).
% 1.67/0.61  fof(f48,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.67/0.61    inference(nnf_transformation,[],[f18])).
% 1.67/0.61  fof(f18,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.67/0.61    inference(flattening,[],[f17])).
% 1.67/0.61  fof(f17,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.67/0.61    inference(ennf_transformation,[],[f1])).
% 1.67/0.61  fof(f1,axiom,(
% 1.67/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.67/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.67/0.61  fof(f278,plain,(
% 1.67/0.61    ~spl11_10 | spl11_9),
% 1.67/0.61    inference(avatar_split_clause,[],[f273,f269,f275])).
% 1.67/0.61  fof(f273,plain,(
% 1.67/0.61    sK9 = k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)) | ~sP3(sK6,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK5)),
% 1.67/0.61    inference(resolution,[],[f245,f127])).
% 1.67/0.61  fof(f127,plain,(
% 1.67/0.61    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,sK5,sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)),
% 1.67/0.61    inference(forward_demodulation,[],[f74,f73])).
% 1.67/0.61  fof(f74,plain,(
% 1.67/0.61    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10)),sK9)),
% 1.67/0.61    inference(cnf_transformation,[],[f38])).
% 1.67/0.61  fof(f245,plain,(
% 1.67/0.61    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f244,f100])).
% 1.67/0.61  fof(f244,plain,(
% 1.67/0.61    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3)) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f239,f101])).
% 1.67/0.61  fof(f239,plain,(
% 1.67/0.61    ( ! [X2,X3,X1] : (sK9 = k3_tmap_1(X1,sK6,X2,sK7,X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),k3_tmap_1(X1,sK6,X2,sK7,X3),sK9) | ~v1_funct_2(k3_tmap_1(X1,sK6,X2,sK7,X3),u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(k3_tmap_1(X1,sK6,X2,sK7,X3)) | ~sP3(sK6,sK7,X3,X2,X1)) )),
% 1.67/0.61    inference(resolution,[],[f234,f102])).
% 1.67/0.61  fof(f234,plain,(
% 1.67/0.61    ( ! [X44] : (~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | sK9 = X44 | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f233,f65])).
% 1.67/0.61  fof(f233,plain,(
% 1.67/0.61    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | sK9 = X44 | ~v1_funct_1(sK9) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.67/0.61    inference(subsumption_resolution,[],[f213,f66])).
% 1.67/0.61  fof(f213,plain,(
% 1.67/0.61    ( ! [X44] : (~r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK6),X44,sK9) | sK9 = X44 | ~v1_funct_2(sK9,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(sK9) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) | ~v1_funct_2(X44,u1_struct_0(sK7),u1_struct_0(sK6)) | ~v1_funct_1(X44)) )),
% 1.67/0.61    inference(resolution,[],[f98,f68])).
% 1.67/0.61  fof(f174,plain,(
% 1.67/0.61    spl11_5),
% 1.67/0.61    inference(avatar_contradiction_clause,[],[f173])).
% 1.67/0.61  fof(f173,plain,(
% 1.67/0.61    $false | spl11_5),
% 1.67/0.61    inference(subsumption_resolution,[],[f172,f53])).
% 1.67/0.61  fof(f172,plain,(
% 1.67/0.61    v2_struct_0(sK5) | spl11_5),
% 1.67/0.61    inference(subsumption_resolution,[],[f171,f55])).
% 1.67/0.61  fof(f171,plain,(
% 1.67/0.61    ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.67/0.61    inference(subsumption_resolution,[],[f170,f59])).
% 1.67/0.61  fof(f170,plain,(
% 1.67/0.61    v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.67/0.61    inference(subsumption_resolution,[],[f169,f61])).
% 1.67/0.61  fof(f169,plain,(
% 1.67/0.61    ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.67/0.61    inference(subsumption_resolution,[],[f168,f62])).
% 1.67/0.61  fof(f168,plain,(
% 1.67/0.61    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.67/0.61    inference(subsumption_resolution,[],[f167,f64])).
% 1.67/0.61  fof(f167,plain,(
% 1.67/0.61    ~m1_pre_topc(sK8,sK5) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | spl11_5),
% 1.67/0.61    inference(resolution,[],[f97,f134])).
% 1.67/0.61  fof(f134,plain,(
% 1.67/0.61    ~sP2(sK5,sK8,sK7) | spl11_5),
% 1.67/0.61    inference(avatar_component_clause,[],[f132])).
% 1.67/0.61  fof(f132,plain,(
% 1.67/0.61    spl11_5 <=> sP2(sK5,sK8,sK7)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.67/0.61  fof(f97,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f27])).
% 1.67/0.61  fof(f27,plain,(
% 1.67/0.61    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.61    inference(definition_folding,[],[f16,f26])).
% 1.67/0.61  fof(f26,plain,(
% 1.67/0.61    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 1.67/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.67/0.61  fof(f16,plain,(
% 1.67/0.61    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.61    inference(flattening,[],[f15])).
% 1.67/0.61  fof(f15,plain,(
% 1.67/0.61    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.61    inference(ennf_transformation,[],[f3])).
% 1.67/0.61  fof(f3,axiom,(
% 1.67/0.61    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.67/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.67/0.61  fof(f145,plain,(
% 1.67/0.61    ~spl11_5 | spl11_7),
% 1.67/0.61    inference(avatar_split_clause,[],[f140,f142,f132])).
% 1.67/0.61  fof(f140,plain,(
% 1.67/0.61    m1_pre_topc(sK5,sK5) | ~sP2(sK5,sK8,sK7)),
% 1.67/0.61    inference(superposition,[],[f96,f73])).
% 1.67/0.61  fof(f96,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP2(X0,X1,X2)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f47])).
% 1.67/0.61  fof(f47,plain,(
% 1.67/0.61    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP2(X0,X1,X2))),
% 1.67/0.61    inference(rectify,[],[f46])).
% 1.67/0.61  fof(f46,plain,(
% 1.67/0.61    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 1.67/0.61    inference(nnf_transformation,[],[f26])).
% 1.67/0.61  fof(f126,plain,(
% 1.67/0.61    ~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f76,f123,f119,f115,f111])).
% 1.67/0.61  fof(f76,plain,(
% 1.67/0.61    ~m1_subset_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~v5_pre_topc(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),sK5,sK6) | ~v1_funct_2(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10),u1_struct_0(sK5),u1_struct_0(sK6)) | ~v1_funct_1(k10_tmap_1(sK5,sK6,sK7,sK8,sK9,sK10))),
% 1.67/0.61    inference(cnf_transformation,[],[f38])).
% 1.67/0.61  % SZS output end Proof for theBenchmark
% 1.67/0.61  % (12796)------------------------------
% 1.67/0.61  % (12796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.61  % (12796)Termination reason: Refutation
% 1.67/0.61  
% 1.67/0.61  % (12796)Memory used [KB]: 7036
% 1.67/0.61  % (12796)Time elapsed: 0.192 s
% 1.67/0.61  % (12796)------------------------------
% 1.67/0.61  % (12796)------------------------------
% 1.67/0.61  % (12790)Success in time 0.245 s
%------------------------------------------------------------------------------

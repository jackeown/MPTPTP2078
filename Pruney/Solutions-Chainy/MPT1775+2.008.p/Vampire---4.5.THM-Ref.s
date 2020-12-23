%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  213 (1026 expanded)
%              Number of leaves         :   34 ( 479 expanded)
%              Depth                    :   30
%              Number of atoms          : 1527 (19305 expanded)
%              Number of equality atoms :   42 (1139 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f438,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f121,f138,f139,f157,f158,f327,f399,f405,f414,f437])).

fof(f437,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f435,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      | ~ r1_tmap_1(sK5,sK3,sK6,sK7) )
    & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      | r1_tmap_1(sK5,sK3,sK6,sK7) )
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_pre_topc(sK4,sK5)
    & v1_tsep_1(sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f46,f53,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X1,X4,X5) )
                            & ( r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X1,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK3,X4,X5) )
                          & ( r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK3,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK3,X4,X5) )
                        & ( r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK3,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & v1_tsep_1(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                        | ~ r1_tmap_1(X3,sK3,X4,X5) )
                      & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                        | r1_tmap_1(X3,sK3,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK4,X3)
              & v1_tsep_1(sK4,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                      | ~ r1_tmap_1(X3,sK3,X4,X5) )
                    & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                      | r1_tmap_1(X3,sK3,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK4,X3)
            & v1_tsep_1(sK4,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                    | ~ r1_tmap_1(sK5,sK3,X4,X5) )
                  & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                    | r1_tmap_1(sK5,sK3,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & m1_pre_topc(sK4,sK5)
          & v1_tsep_1(sK4,sK5)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                  | ~ r1_tmap_1(sK5,sK3,X4,X5) )
                & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                  | r1_tmap_1(sK5,sK3,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & m1_pre_topc(sK4,sK5)
        & v1_tsep_1(sK4,sK5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
                | ~ r1_tmap_1(sK5,sK3,sK6,X5) )
              & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
                | r1_tmap_1(sK5,sK3,sK6,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & m1_pre_topc(sK4,sK5)
      & v1_tsep_1(sK4,sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
              | ~ r1_tmap_1(sK5,sK3,sK6,X5) )
            & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
              | r1_tmap_1(sK5,sK3,sK6,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
            | ~ r1_tmap_1(sK5,sK3,sK6,sK7) )
          & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
            | r1_tmap_1(sK5,sK3,sK6,sK7) )
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
          | ~ r1_tmap_1(sK5,sK3,sK6,sK7) )
        & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
          | r1_tmap_1(sK5,sK3,sK6,sK7) )
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
        | ~ r1_tmap_1(sK5,sK3,sK6,sK7) )
      & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
        | r1_tmap_1(sK5,sK3,sK6,sK7) )
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f435,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f434,f65])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f434,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f433,f66])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f433,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f432,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f432,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f431,f68])).

fof(f68,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f431,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f430,f69])).

fof(f69,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f430,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f429,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f429,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f428,f73])).

fof(f73,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f428,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f427,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f427,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f426,f74])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f426,plain,
    ( ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f425,f75])).

fof(f75,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f425,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f424,f76])).

fof(f76,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f424,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f423,f79])).

fof(f79,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f423,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f422,f122])).

fof(f122,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f80,f81])).

fof(f81,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f422,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f421,f78])).

fof(f78,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f421,plain,
    ( ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f420,f114])).

fof(f114,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl10_1
  <=> r1_tmap_1(sK5,sK3,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f420,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl10_2 ),
    inference(resolution,[],[f415,f268])).

fof(f268,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f108,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
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
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f415,plain,
    ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | spl10_2 ),
    inference(forward_demodulation,[],[f119,f81])).

fof(f119,plain,
    ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl10_2
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f414,plain,
    ( ~ spl10_3
    | ~ spl10_5
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_5
    | spl10_16 ),
    inference(subsumption_resolution,[],[f412,f77])).

fof(f77,plain,(
    v1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f412,plain,
    ( ~ v1_tsep_1(sK4,sK5)
    | ~ spl10_3
    | ~ spl10_5
    | spl10_16 ),
    inference(subsumption_resolution,[],[f411,f78])).

fof(f411,plain,
    ( ~ m1_pre_topc(sK4,sK5)
    | ~ v1_tsep_1(sK4,sK5)
    | ~ spl10_3
    | ~ spl10_5
    | spl10_16 ),
    inference(resolution,[],[f410,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f410,plain,
    ( ~ sP0(sK5,sK4)
    | ~ spl10_3
    | ~ spl10_5
    | spl10_16 ),
    inference(subsumption_resolution,[],[f409,f131])).

fof(f131,plain,
    ( l1_pre_topc(sK5)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl10_3
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f409,plain,
    ( ~ sP0(sK5,sK4)
    | ~ l1_pre_topc(sK5)
    | ~ spl10_5
    | spl10_16 ),
    inference(subsumption_resolution,[],[f408,f150])).

fof(f150,plain,
    ( v2_pre_topc(sK5)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl10_5
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f408,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ sP0(sK5,sK4)
    | ~ l1_pre_topc(sK5)
    | spl10_16 ),
    inference(resolution,[],[f398,f210])).

fof(f210,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(u1_struct_0(X2),X3)
      | ~ v2_pre_topc(X3)
      | ~ sP0(X3,X2)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f209,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f209,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ sP0(X3,X2)
      | v3_pre_topc(u1_struct_0(X2),X3) ) ),
    inference(resolution,[],[f207,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X0,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f207,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f109,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f32,f43,f42])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f398,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK5)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl10_16
  <=> v3_pre_topc(u1_struct_0(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f405,plain,
    ( spl10_11
    | spl10_15 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl10_11
    | spl10_15 ),
    inference(subsumption_resolution,[],[f403,f122])).

fof(f403,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | spl10_11
    | spl10_15 ),
    inference(subsumption_resolution,[],[f402,f226])).

fof(f226,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_11 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl10_11
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f402,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | spl10_15 ),
    inference(resolution,[],[f394,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f394,plain,
    ( ~ r2_hidden(sK7,u1_struct_0(sK4))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl10_15
  <=> r2_hidden(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f399,plain,
    ( ~ spl10_15
    | ~ spl10_16
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f390,f130,f117,f113,f396,f392])).

fof(f390,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f389,f78])).

fof(f389,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,sK5)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f374,f110])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f374,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
        | ~ v3_pre_topc(u1_struct_0(X0),sK5)
        | ~ r2_hidden(sK7,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK5) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f372,f131])).

fof(f372,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),sK5)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
        | ~ m1_pre_topc(X0,sK5)
        | ~ l1_pre_topc(sK5) )
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f362,f85])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK4)) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f361,f64])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f360,f65])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f359,f66])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f358,f67])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f357,f68])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f356,f69])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f355,f70])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f354,f72])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f353,f73])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f352,f74])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f351,f75])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f350,f76])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f349,f78])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f348,f122])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f345,f115])).

fof(f115,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f345,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK5,sK3,sK6,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_2 ),
    inference(resolution,[],[f333,f123])).

fof(f123,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f118,f81])).

fof(f118,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f333,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f332,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f332,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f91])).

fof(f106,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f88])).

% (24094)Refutation not found, incomplete strategy% (24094)------------------------------
% (24094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24094)Termination reason: Refutation not found, incomplete strategy

% (24094)Memory used [KB]: 10746
% (24094)Time elapsed: 0.095 s
% (24094)------------------------------
% (24094)------------------------------
fof(f88,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f327,plain,
    ( ~ spl10_11
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f326,f153,f134,f225])).

fof(f134,plain,
    ( spl10_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f153,plain,
    ( spl10_6
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f326,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f316,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f316,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f315,f70])).

fof(f315,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f307,f155])).

fof(f155,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f307,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f305,f122])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f302,f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK9(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK9(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f259,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK9(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK9(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK9(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK9(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X2,sK9(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f233,f100])).

fof(f233,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_connsp_2(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ v1_xboole_0(u1_struct_0(X5))
      | ~ r2_hidden(X7,X4) ) ),
    inference(resolution,[],[f99,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f158,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f146,f149])).

fof(f146,plain,(
    v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f145,f65])).

fof(f145,plain,
    ( v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f141,f66])).

fof(f141,plain,
    ( v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f90,f73])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f157,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f144,f153])).

fof(f144,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f143,f65])).

fof(f143,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f140,f66])).

fof(f140,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f90,f71])).

fof(f71,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f139,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f128,f130])).

fof(f128,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f125,f66])).

fof(f125,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f84,f73])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f138,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f127,f134])).

fof(f127,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f124,f66])).

fof(f124,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f84,f71])).

fof(f121,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f82,f117,f113])).

fof(f82,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f120,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f83,f117,f113])).

% (24096)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f83,plain,
    ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (24106)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (24107)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (24105)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (24114)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (24095)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (24101)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (24099)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (24108)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (24119)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (24097)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (24094)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (24098)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (24117)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (24095)Refutation not found, incomplete strategy% (24095)------------------------------
% 0.20/0.51  % (24095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24103)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (24095)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24095)Memory used [KB]: 10746
% 0.20/0.51  % (24095)Time elapsed: 0.097 s
% 0.20/0.51  % (24095)------------------------------
% 0.20/0.51  % (24095)------------------------------
% 0.20/0.51  % (24100)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (24101)Refutation not found, incomplete strategy% (24101)------------------------------
% 0.20/0.51  % (24101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24110)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (24099)Refutation not found, incomplete strategy% (24099)------------------------------
% 0.20/0.51  % (24099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24099)Memory used [KB]: 6268
% 0.20/0.51  % (24099)Time elapsed: 0.106 s
% 0.20/0.51  % (24099)------------------------------
% 0.20/0.51  % (24099)------------------------------
% 0.20/0.51  % (24098)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (24115)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (24109)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (24101)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24101)Memory used [KB]: 1791
% 0.20/0.52  % (24101)Time elapsed: 0.096 s
% 0.20/0.52  % (24101)------------------------------
% 0.20/0.52  % (24101)------------------------------
% 0.20/0.52  % (24113)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.31/0.52  % (24118)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f438,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(avatar_sat_refutation,[],[f120,f121,f138,f139,f157,f158,f327,f399,f405,f414,f437])).
% 1.31/0.53  fof(f437,plain,(
% 1.31/0.53    ~spl10_1 | spl10_2),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f436])).
% 1.31/0.53  fof(f436,plain,(
% 1.31/0.53    $false | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f435,f64])).
% 1.31/0.53  fof(f64,plain,(
% 1.31/0.53    ~v2_struct_0(sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f54,plain,(
% 1.31/0.53    (((((((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK3,sK6,sK7)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK3,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & v1_tsep_1(sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f46,f53,f52,f51,f50,f49,f48,f47])).
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f48,plain,(
% 1.31/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK3,X4,X5)) & (r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) | r1_tmap_1(X3,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f49,plain,(
% 1.31/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK3,X4,X5)) & (r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) | r1_tmap_1(X3,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) | ~r1_tmap_1(X3,sK3,X4,X5)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) | r1_tmap_1(X3,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & v1_tsep_1(sK4,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f50,plain,(
% 1.31/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) | ~r1_tmap_1(X3,sK3,X4,X5)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) | r1_tmap_1(X3,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & v1_tsep_1(sK4,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) | ~r1_tmap_1(sK5,sK3,X4,X5)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) | r1_tmap_1(sK5,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & v1_tsep_1(sK4,sK5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f51,plain,(
% 1.31/0.53    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) | ~r1_tmap_1(sK5,sK3,X4,X5)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) | r1_tmap_1(sK5,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & v1_tsep_1(sK4,sK5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK3,sK6,X5)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK3,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & v1_tsep_1(sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f52,plain,(
% 1.31/0.53    ? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK3,sK6,X5)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK3,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK3,sK6,sK7)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK3,sK6,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f53,plain,(
% 1.31/0.53    ? [X6] : ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK3,sK6,sK7)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK3,sK6,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK3,sK6,sK7)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK3,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f46,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f45])).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.31/0.53    inference(nnf_transformation,[],[f18])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f17])).
% 1.31/0.53  fof(f17,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,negated_conjecture,(
% 1.31/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.31/0.53    inference(negated_conjecture,[],[f15])).
% 1.31/0.53  fof(f15,conjecture,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.31/0.53  fof(f435,plain,(
% 1.31/0.53    v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f434,f65])).
% 1.31/0.53  fof(f65,plain,(
% 1.31/0.53    v2_pre_topc(sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f434,plain,(
% 1.31/0.53    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f433,f66])).
% 1.31/0.53  fof(f66,plain,(
% 1.31/0.53    l1_pre_topc(sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f433,plain,(
% 1.31/0.53    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f432,f67])).
% 1.31/0.53  fof(f67,plain,(
% 1.31/0.53    ~v2_struct_0(sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f432,plain,(
% 1.31/0.53    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f431,f68])).
% 1.31/0.53  fof(f68,plain,(
% 1.31/0.53    v2_pre_topc(sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f431,plain,(
% 1.31/0.53    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f430,f69])).
% 1.31/0.53  fof(f69,plain,(
% 1.31/0.53    l1_pre_topc(sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f430,plain,(
% 1.31/0.53    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f429,f72])).
% 1.31/0.53  fof(f72,plain,(
% 1.31/0.53    ~v2_struct_0(sK5)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f429,plain,(
% 1.31/0.53    v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f428,f73])).
% 1.31/0.53  fof(f73,plain,(
% 1.31/0.53    m1_pre_topc(sK5,sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f428,plain,(
% 1.31/0.53    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f427,f70])).
% 1.31/0.53  fof(f70,plain,(
% 1.31/0.53    ~v2_struct_0(sK4)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f427,plain,(
% 1.31/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f426,f74])).
% 1.31/0.53  fof(f74,plain,(
% 1.31/0.53    v1_funct_1(sK6)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f426,plain,(
% 1.31/0.53    ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f425,f75])).
% 1.31/0.53  fof(f75,plain,(
% 1.31/0.53    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f425,plain,(
% 1.31/0.53    ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f424,f76])).
% 1.31/0.53  fof(f76,plain,(
% 1.31/0.53    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f424,plain,(
% 1.31/0.53    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f423,f79])).
% 1.31/0.53  fof(f79,plain,(
% 1.31/0.53    m1_subset_1(sK7,u1_struct_0(sK5))),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f423,plain,(
% 1.31/0.53    ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f422,f122])).
% 1.31/0.53  fof(f122,plain,(
% 1.31/0.53    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.31/0.53    inference(forward_demodulation,[],[f80,f81])).
% 1.31/0.53  fof(f81,plain,(
% 1.31/0.53    sK7 = sK8),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f80,plain,(
% 1.31/0.53    m1_subset_1(sK8,u1_struct_0(sK4))),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f422,plain,(
% 1.31/0.53    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f421,f78])).
% 1.31/0.53  fof(f78,plain,(
% 1.31/0.53    m1_pre_topc(sK4,sK5)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f421,plain,(
% 1.31/0.53    ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f420,f114])).
% 1.31/0.53  fof(f114,plain,(
% 1.31/0.53    r1_tmap_1(sK5,sK3,sK6,sK7) | ~spl10_1),
% 1.31/0.53    inference(avatar_component_clause,[],[f113])).
% 1.31/0.53  fof(f113,plain,(
% 1.31/0.53    spl10_1 <=> r1_tmap_1(sK5,sK3,sK6,sK7)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.31/0.53  fof(f420,plain,(
% 1.31/0.53    ~r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl10_2),
% 1.31/0.53    inference(resolution,[],[f415,f268])).
% 1.31/0.53  fof(f268,plain,(
% 1.31/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f108,f91])).
% 1.31/0.53  fof(f91,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f12])).
% 1.31/0.53  fof(f12,axiom,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.31/0.53  fof(f108,plain,(
% 1.31/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(equality_resolution,[],[f89])).
% 1.31/0.53  fof(f89,plain,(
% 1.31/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f26])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f25])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,axiom,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 1.31/0.53  fof(f415,plain,(
% 1.31/0.53    ~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | spl10_2),
% 1.31/0.53    inference(forward_demodulation,[],[f119,f81])).
% 1.31/0.53  fof(f119,plain,(
% 1.31/0.53    ~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | spl10_2),
% 1.31/0.53    inference(avatar_component_clause,[],[f117])).
% 1.31/0.53  fof(f117,plain,(
% 1.31/0.53    spl10_2 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.31/0.53  fof(f414,plain,(
% 1.31/0.53    ~spl10_3 | ~spl10_5 | spl10_16),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f413])).
% 1.31/0.53  fof(f413,plain,(
% 1.31/0.53    $false | (~spl10_3 | ~spl10_5 | spl10_16)),
% 1.31/0.53    inference(subsumption_resolution,[],[f412,f77])).
% 1.31/0.53  fof(f77,plain,(
% 1.31/0.53    v1_tsep_1(sK4,sK5)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f412,plain,(
% 1.31/0.53    ~v1_tsep_1(sK4,sK5) | (~spl10_3 | ~spl10_5 | spl10_16)),
% 1.31/0.53    inference(subsumption_resolution,[],[f411,f78])).
% 1.31/0.53  fof(f411,plain,(
% 1.31/0.53    ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,sK5) | (~spl10_3 | ~spl10_5 | spl10_16)),
% 1.31/0.53    inference(resolution,[],[f410,f96])).
% 1.31/0.53  fof(f96,plain,(
% 1.31/0.53    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f59])).
% 1.31/0.53  fof(f59,plain,(
% 1.31/0.53    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 1.31/0.53    inference(flattening,[],[f58])).
% 1.31/0.53  fof(f58,plain,(
% 1.31/0.53    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 1.31/0.53    inference(nnf_transformation,[],[f42])).
% 1.31/0.53  fof(f42,plain,(
% 1.31/0.53    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 1.31/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.31/0.53  fof(f410,plain,(
% 1.31/0.53    ~sP0(sK5,sK4) | (~spl10_3 | ~spl10_5 | spl10_16)),
% 1.31/0.53    inference(subsumption_resolution,[],[f409,f131])).
% 1.31/0.53  fof(f131,plain,(
% 1.31/0.53    l1_pre_topc(sK5) | ~spl10_3),
% 1.31/0.53    inference(avatar_component_clause,[],[f130])).
% 1.31/0.53  fof(f130,plain,(
% 1.31/0.53    spl10_3 <=> l1_pre_topc(sK5)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.31/0.53  fof(f409,plain,(
% 1.31/0.53    ~sP0(sK5,sK4) | ~l1_pre_topc(sK5) | (~spl10_5 | spl10_16)),
% 1.31/0.53    inference(subsumption_resolution,[],[f408,f150])).
% 1.31/0.53  fof(f150,plain,(
% 1.31/0.53    v2_pre_topc(sK5) | ~spl10_5),
% 1.31/0.53    inference(avatar_component_clause,[],[f149])).
% 1.31/0.53  fof(f149,plain,(
% 1.31/0.53    spl10_5 <=> v2_pre_topc(sK5)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.31/0.53  fof(f408,plain,(
% 1.31/0.53    ~v2_pre_topc(sK5) | ~sP0(sK5,sK4) | ~l1_pre_topc(sK5) | spl10_16),
% 1.31/0.53    inference(resolution,[],[f398,f210])).
% 1.31/0.53  fof(f210,plain,(
% 1.31/0.53    ( ! [X2,X3] : (v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3) | ~sP0(X3,X2) | ~l1_pre_topc(X3)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f209,f95])).
% 1.31/0.53  fof(f95,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | m1_pre_topc(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f59])).
% 1.31/0.53  fof(f209,plain,(
% 1.31/0.53    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~sP0(X3,X2) | v3_pre_topc(u1_struct_0(X2),X3)) )),
% 1.31/0.53    inference(resolution,[],[f207,f92])).
% 1.31/0.53  fof(f92,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X0,X2) | v3_pre_topc(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f57])).
% 1.31/0.53  fof(f57,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 1.31/0.53    inference(rectify,[],[f56])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 1.31/0.53    inference(nnf_transformation,[],[f43])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 1.31/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.31/0.53  fof(f207,plain,(
% 1.31/0.53    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f109,f85])).
% 1.31/0.53  fof(f85,plain,(
% 1.31/0.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f20])).
% 1.31/0.53  fof(f20,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.31/0.53  fof(f109,plain,(
% 1.31/0.53    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.53    inference(equality_resolution,[],[f97])).
% 1.31/0.53  fof(f97,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f44])).
% 1.31/0.53  fof(f44,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.53    inference(definition_folding,[],[f32,f43,f42])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f31])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.31/0.53  fof(f398,plain,(
% 1.31/0.53    ~v3_pre_topc(u1_struct_0(sK4),sK5) | spl10_16),
% 1.31/0.53    inference(avatar_component_clause,[],[f396])).
% 1.31/0.53  fof(f396,plain,(
% 1.31/0.53    spl10_16 <=> v3_pre_topc(u1_struct_0(sK4),sK5)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.31/0.53  fof(f405,plain,(
% 1.31/0.53    spl10_11 | spl10_15),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f404])).
% 1.31/0.53  fof(f404,plain,(
% 1.31/0.53    $false | (spl10_11 | spl10_15)),
% 1.31/0.53    inference(subsumption_resolution,[],[f403,f122])).
% 1.31/0.53  fof(f403,plain,(
% 1.31/0.53    ~m1_subset_1(sK7,u1_struct_0(sK4)) | (spl10_11 | spl10_15)),
% 1.31/0.53    inference(subsumption_resolution,[],[f402,f226])).
% 1.31/0.53  fof(f226,plain,(
% 1.31/0.53    ~v1_xboole_0(u1_struct_0(sK4)) | spl10_11),
% 1.31/0.53    inference(avatar_component_clause,[],[f225])).
% 1.31/0.53  fof(f225,plain,(
% 1.31/0.53    spl10_11 <=> v1_xboole_0(u1_struct_0(sK4))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.31/0.53  fof(f402,plain,(
% 1.31/0.53    v1_xboole_0(u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | spl10_15),
% 1.31/0.53    inference(resolution,[],[f394,f98])).
% 1.31/0.53  fof(f98,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f34])).
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.31/0.53    inference(flattening,[],[f33])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.31/0.53  fof(f394,plain,(
% 1.31/0.53    ~r2_hidden(sK7,u1_struct_0(sK4)) | spl10_15),
% 1.31/0.53    inference(avatar_component_clause,[],[f392])).
% 1.31/0.53  fof(f392,plain,(
% 1.31/0.53    spl10_15 <=> r2_hidden(sK7,u1_struct_0(sK4))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.31/0.53  fof(f399,plain,(
% 1.31/0.53    ~spl10_15 | ~spl10_16 | spl10_1 | ~spl10_2 | ~spl10_3),
% 1.31/0.53    inference(avatar_split_clause,[],[f390,f130,f117,f113,f396,f392])).
% 1.31/0.53  fof(f390,plain,(
% 1.31/0.53    ~v3_pre_topc(u1_struct_0(sK4),sK5) | ~r2_hidden(sK7,u1_struct_0(sK4)) | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f389,f78])).
% 1.31/0.53  fof(f389,plain,(
% 1.31/0.53    ~v3_pre_topc(u1_struct_0(sK4),sK5) | ~r2_hidden(sK7,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK5) | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.31/0.53    inference(resolution,[],[f374,f110])).
% 1.31/0.53  fof(f110,plain,(
% 1.31/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.53    inference(equality_resolution,[],[f102])).
% 1.31/0.53  fof(f102,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f63])).
% 1.31/0.53  fof(f63,plain,(
% 1.31/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.53    inference(flattening,[],[f62])).
% 1.31/0.53  fof(f62,plain,(
% 1.31/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.53    inference(nnf_transformation,[],[f1])).
% 1.31/0.53  fof(f1,axiom,(
% 1.31/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.53  fof(f374,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) | ~v3_pre_topc(u1_struct_0(X0),sK5) | ~r2_hidden(sK7,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK5)) ) | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f372,f131])).
% 1.31/0.53  fof(f372,plain,(
% 1.31/0.53    ( ! [X0] : (~r2_hidden(sK7,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),sK5) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(resolution,[],[f362,f85])).
% 1.31/0.53  fof(f362,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~r1_tarski(X0,u1_struct_0(sK4))) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f361,f64])).
% 1.31/0.53  fof(f361,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f360,f65])).
% 1.31/0.53  fof(f360,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f359,f66])).
% 1.31/0.53  fof(f359,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f358,f67])).
% 1.31/0.53  fof(f358,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f357,f68])).
% 1.31/0.53  fof(f357,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f356,f69])).
% 1.31/0.53  fof(f356,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f355,f70])).
% 1.31/0.53  fof(f355,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f354,f72])).
% 1.31/0.53  fof(f354,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f353,f73])).
% 1.31/0.53  fof(f353,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f352,f74])).
% 1.31/0.53  fof(f352,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f351,f75])).
% 1.31/0.53  fof(f351,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f350,f76])).
% 1.31/0.53  fof(f350,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f349,f78])).
% 1.31/0.53  fof(f349,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f348,f122])).
% 1.31/0.53  fof(f348,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f345,f115])).
% 1.31/0.53  fof(f115,plain,(
% 1.31/0.53    ~r1_tmap_1(sK5,sK3,sK6,sK7) | spl10_1),
% 1.31/0.53    inference(avatar_component_clause,[],[f113])).
% 1.31/0.53  fof(f345,plain,(
% 1.31/0.53    ( ! [X0] : (r1_tmap_1(sK5,sK3,sK6,sK7) | ~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl10_2),
% 1.31/0.53    inference(resolution,[],[f333,f123])).
% 1.31/0.53  fof(f123,plain,(
% 1.31/0.53    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | ~spl10_2),
% 1.31/0.53    inference(forward_demodulation,[],[f118,f81])).
% 1.31/0.53  fof(f118,plain,(
% 1.31/0.53    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~spl10_2),
% 1.31/0.53    inference(avatar_component_clause,[],[f117])).
% 1.31/0.53  fof(f333,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f332,f104])).
% 1.31/0.53  fof(f104,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f40])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.31/0.53    inference(flattening,[],[f39])).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.31/0.53  fof(f332,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f106,f91])).
% 1.31/0.53  fof(f106,plain,(
% 1.31/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(equality_resolution,[],[f88])).
% 1.31/0.53  % (24094)Refutation not found, incomplete strategy% (24094)------------------------------
% 1.31/0.53  % (24094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (24094)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (24094)Memory used [KB]: 10746
% 1.31/0.53  % (24094)Time elapsed: 0.095 s
% 1.31/0.53  % (24094)------------------------------
% 1.31/0.53  % (24094)------------------------------
% 1.31/0.53  fof(f88,plain,(
% 1.31/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f55])).
% 1.31/0.53  fof(f55,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(nnf_transformation,[],[f24])).
% 1.31/0.53  fof(f24,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f23])).
% 1.31/0.53  fof(f23,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f14])).
% 1.31/0.53  fof(f14,axiom,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 1.31/0.53  fof(f327,plain,(
% 1.31/0.53    ~spl10_11 | ~spl10_4 | ~spl10_6),
% 1.31/0.53    inference(avatar_split_clause,[],[f326,f153,f134,f225])).
% 1.31/0.53  fof(f134,plain,(
% 1.31/0.53    spl10_4 <=> l1_pre_topc(sK4)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.31/0.53  fof(f153,plain,(
% 1.31/0.53    spl10_6 <=> v2_pre_topc(sK4)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.31/0.53  fof(f326,plain,(
% 1.31/0.53    ~v1_xboole_0(u1_struct_0(sK4)) | (~spl10_4 | ~spl10_6)),
% 1.31/0.53    inference(subsumption_resolution,[],[f316,f136])).
% 1.31/0.53  fof(f136,plain,(
% 1.31/0.53    l1_pre_topc(sK4) | ~spl10_4),
% 1.31/0.53    inference(avatar_component_clause,[],[f134])).
% 1.31/0.53  fof(f316,plain,(
% 1.31/0.53    ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~spl10_6),
% 1.31/0.53    inference(subsumption_resolution,[],[f315,f70])).
% 1.31/0.53  fof(f315,plain,(
% 1.31/0.53    v2_struct_0(sK4) | ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~spl10_6),
% 1.31/0.53    inference(subsumption_resolution,[],[f307,f155])).
% 1.31/0.53  fof(f155,plain,(
% 1.31/0.53    v2_pre_topc(sK4) | ~spl10_6),
% 1.31/0.53    inference(avatar_component_clause,[],[f153])).
% 1.31/0.53  fof(f307,plain,(
% 1.31/0.53    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4)),
% 1.31/0.53    inference(resolution,[],[f305,f122])).
% 1.31/0.53  fof(f305,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.31/0.53    inference(duplicate_literal_removal,[],[f303])).
% 1.31/0.53  fof(f303,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(resolution,[],[f302,f267])).
% 1.31/0.53  fof(f267,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK9(X1,X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.31/0.53    inference(duplicate_literal_removal,[],[f266])).
% 1.31/0.53  fof(f266,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK9(X1,X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.31/0.53    inference(resolution,[],[f259,f100])).
% 1.31/0.53  fof(f100,plain,(
% 1.31/0.53    ( ! [X0,X1] : (m1_connsp_2(sK9(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f61])).
% 1.31/0.53  fof(f61,plain,(
% 1.31/0.53    ! [X0,X1] : (m1_connsp_2(sK9(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f60])).
% 1.31/0.53  fof(f60,plain,(
% 1.31/0.53    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK9(X0,X1),X0,X1))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f37])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 1.31/0.53  fof(f259,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f86,f99])).
% 1.31/0.53  fof(f99,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f7])).
% 1.31/0.53  fof(f7,axiom,(
% 1.31/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.31/0.53  fof(f86,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.53    inference(flattening,[],[f21])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 1.31/0.53  fof(f302,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK9(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.31/0.53    inference(duplicate_literal_removal,[],[f301])).
% 1.31/0.53  fof(f301,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~r2_hidden(X2,sK9(X1,X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.31/0.53    inference(resolution,[],[f233,f100])).
% 1.31/0.53  fof(f233,plain,(
% 1.31/0.53    ( ! [X6,X4,X7,X5] : (~m1_connsp_2(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~v1_xboole_0(u1_struct_0(X5)) | ~r2_hidden(X7,X4)) )),
% 1.31/0.53    inference(resolution,[],[f99,f105])).
% 1.31/0.53  fof(f105,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f41])).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.31/0.53  fof(f158,plain,(
% 1.31/0.53    spl10_5),
% 1.31/0.53    inference(avatar_split_clause,[],[f146,f149])).
% 1.31/0.53  fof(f146,plain,(
% 1.31/0.53    v2_pre_topc(sK5)),
% 1.31/0.53    inference(subsumption_resolution,[],[f145,f65])).
% 1.31/0.53  fof(f145,plain,(
% 1.31/0.53    v2_pre_topc(sK5) | ~v2_pre_topc(sK2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f141,f66])).
% 1.31/0.53  fof(f141,plain,(
% 1.31/0.53    v2_pre_topc(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.31/0.53    inference(resolution,[],[f90,f73])).
% 1.31/0.53  fof(f90,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.31/0.53  fof(f157,plain,(
% 1.31/0.53    spl10_6),
% 1.31/0.53    inference(avatar_split_clause,[],[f144,f153])).
% 1.31/0.53  fof(f144,plain,(
% 1.31/0.53    v2_pre_topc(sK4)),
% 1.31/0.53    inference(subsumption_resolution,[],[f143,f65])).
% 1.31/0.53  fof(f143,plain,(
% 1.31/0.53    v2_pre_topc(sK4) | ~v2_pre_topc(sK2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f140,f66])).
% 1.31/0.53  fof(f140,plain,(
% 1.31/0.53    v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.31/0.53    inference(resolution,[],[f90,f71])).
% 1.31/0.53  fof(f71,plain,(
% 1.31/0.53    m1_pre_topc(sK4,sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f139,plain,(
% 1.31/0.53    spl10_3),
% 1.31/0.53    inference(avatar_split_clause,[],[f128,f130])).
% 1.31/0.53  fof(f128,plain,(
% 1.31/0.53    l1_pre_topc(sK5)),
% 1.31/0.53    inference(subsumption_resolution,[],[f125,f66])).
% 1.31/0.53  fof(f125,plain,(
% 1.31/0.53    l1_pre_topc(sK5) | ~l1_pre_topc(sK2)),
% 1.31/0.53    inference(resolution,[],[f84,f73])).
% 1.31/0.53  fof(f84,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f19])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f6])).
% 1.31/0.53  fof(f6,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.31/0.53  fof(f138,plain,(
% 1.31/0.53    spl10_4),
% 1.31/0.53    inference(avatar_split_clause,[],[f127,f134])).
% 1.31/0.53  fof(f127,plain,(
% 1.31/0.53    l1_pre_topc(sK4)),
% 1.31/0.53    inference(subsumption_resolution,[],[f124,f66])).
% 1.31/0.53  fof(f124,plain,(
% 1.31/0.53    l1_pre_topc(sK4) | ~l1_pre_topc(sK2)),
% 1.31/0.53    inference(resolution,[],[f84,f71])).
% 1.31/0.53  fof(f121,plain,(
% 1.31/0.53    spl10_1 | spl10_2),
% 1.31/0.53    inference(avatar_split_clause,[],[f82,f117,f113])).
% 1.31/0.53  fof(f82,plain,(
% 1.31/0.53    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK3,sK6,sK7)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  fof(f120,plain,(
% 1.31/0.53    ~spl10_1 | ~spl10_2),
% 1.31/0.53    inference(avatar_split_clause,[],[f83,f117,f113])).
% 1.31/0.53  % (24096)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.31/0.53  fof(f83,plain,(
% 1.31/0.53    ~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 1.31/0.53    inference(cnf_transformation,[],[f54])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (24098)------------------------------
% 1.31/0.53  % (24098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (24098)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (24098)Memory used [KB]: 6396
% 1.31/0.53  % (24098)Time elapsed: 0.108 s
% 1.31/0.53  % (24098)------------------------------
% 1.31/0.53  % (24098)------------------------------
% 1.31/0.53  % (24102)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.31/0.53  % (24093)Success in time 0.172 s
%------------------------------------------------------------------------------

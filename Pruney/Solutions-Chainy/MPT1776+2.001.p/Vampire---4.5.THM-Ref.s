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
% DateTime   : Thu Dec  3 13:18:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 963 expanded)
%              Number of leaves         :   29 ( 457 expanded)
%              Depth                    :   31
%              Number of atoms          : 1424 (19644 expanded)
%              Number of equality atoms :   42 (1118 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f112,f129,f148,f268,f345,f349,f357,f382])).

fof(f382,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f380,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
      | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
    & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
      | r1_tmap_1(sK5,sK2,sK6,sK7) )
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_pre_topc(sK4,sK5)
    & m1_pre_topc(sK4,sK3)
    & v1_tsep_1(sK4,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f40,f47,f46,f45,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                              ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK2,X4,X5) )
                              & ( r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK2,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK2,X4,X5) )
                            & ( r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK2,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,X1)
                    & v1_tsep_1(X2,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK2,X4,X5) )
                          & ( r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK2,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,sK3)
                  & v1_tsep_1(X2,sK3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK2,X4,X5) )
                        & ( r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK2,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X2,sK3)
                & v1_tsep_1(X2,sK3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                        | ~ r1_tmap_1(X3,sK2,X4,X5) )
                      & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                        | r1_tmap_1(X3,sK2,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK4,X3)
              & m1_pre_topc(sK4,sK3)
              & v1_tsep_1(sK4,sK3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK3)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                      | ~ r1_tmap_1(X3,sK2,X4,X5) )
                    & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                      | r1_tmap_1(X3,sK2,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK4,X3)
            & m1_pre_topc(sK4,sK3)
            & v1_tsep_1(sK4,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                    | ~ r1_tmap_1(sK5,sK2,X4,X5) )
                  & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                    | r1_tmap_1(sK5,sK2,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & m1_pre_topc(sK4,sK5)
          & m1_pre_topc(sK4,sK3)
          & v1_tsep_1(sK4,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                  | ~ r1_tmap_1(sK5,sK2,X4,X5) )
                & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                  | r1_tmap_1(sK5,sK2,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & m1_pre_topc(sK4,sK5)
        & m1_pre_topc(sK4,sK3)
        & v1_tsep_1(sK4,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
                | ~ r1_tmap_1(sK5,sK2,sK6,X5) )
              & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
                | r1_tmap_1(sK5,sK2,sK6,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & m1_pre_topc(sK4,sK5)
      & m1_pre_topc(sK4,sK3)
      & v1_tsep_1(sK4,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
              | ~ r1_tmap_1(sK5,sK2,sK6,X5) )
            & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
              | r1_tmap_1(sK5,sK2,sK6,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
            | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
          & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
            | r1_tmap_1(sK5,sK2,sK6,sK7) )
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
          | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
        & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
          | r1_tmap_1(sK5,sK2,sK6,sK7) )
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
        | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
      & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
        | r1_tmap_1(sK5,sK2,sK6,sK7) )
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

% (32543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f380,plain,
    ( v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f379,f60])).

fof(f60,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f379,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f378,f61])).

fof(f61,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f378,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f377,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f377,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f376,f57])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f376,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f375,f58])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f375,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f374,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f374,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f373,f65])).

fof(f65,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f373,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f372,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f372,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f371,f66])).

% (32541)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f66,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f371,plain,
    ( ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f370,f67])).

fof(f67,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f370,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f369,f68])).

fof(f68,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f369,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f368,f72])).

fof(f72,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f368,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f367,f113])).

fof(f113,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f367,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f366,f71])).

fof(f71,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f366,plain,
    ( ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f365,f105])).

fof(f105,plain,
    ( r1_tmap_1(sK5,sK2,sK6,sK7)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_1
  <=> r1_tmap_1(sK5,sK2,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f365,plain,
    ( ~ r1_tmap_1(sK5,sK2,sK6,sK7)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_2 ),
    inference(resolution,[],[f358,f249])).

fof(f249,plain,(
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
    inference(subsumption_resolution,[],[f99,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f358,plain,
    ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7)
    | spl9_2 ),
    inference(forward_demodulation,[],[f110,f74])).

fof(f110,plain,
    ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_2
  <=> r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f357,plain,(
    spl9_14 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl9_14 ),
    inference(subsumption_resolution,[],[f355,f69])).

fof(f69,plain,(
    v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f355,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f354,f63])).

fof(f63,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f354,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | spl9_14 ),
    inference(resolution,[],[f353,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f353,plain,
    ( ~ sP0(sK3,sK4)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f352,f61])).

fof(f352,plain,
    ( ~ sP0(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | spl9_14 ),
    inference(subsumption_resolution,[],[f351,f60])).

fof(f351,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ sP0(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | spl9_14 ),
    inference(resolution,[],[f344,f232])).

fof(f232,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(u1_struct_0(X2),X3)
      | ~ v2_pre_topc(X3)
      | ~ sP0(X3,X2)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f231,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ sP0(X3,X2)
      | v3_pre_topc(u1_struct_0(X2),X3) ) ),
    inference(resolution,[],[f229,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X0,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f229,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f100,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f30,f37,f36])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f344,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl9_14
  <=> v3_pre_topc(u1_struct_0(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f349,plain,
    ( spl9_11
    | spl9_13 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl9_11
    | spl9_13 ),
    inference(subsumption_resolution,[],[f347,f113])).

fof(f347,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | spl9_11
    | spl9_13 ),
    inference(subsumption_resolution,[],[f346,f208])).

fof(f208,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl9_11
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f346,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | spl9_13 ),
    inference(resolution,[],[f340,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f340,plain,
    ( ~ r2_hidden(sK7,u1_struct_0(sK4))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl9_13
  <=> r2_hidden(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f345,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f336,f108,f104,f342,f338])).

fof(f336,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f335,f63])).

fof(f335,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f331,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f331,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ r2_hidden(sK7,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f329,f61])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f328,f78])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK4)) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f327,f56])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f326,f57])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f325,f58])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f324,f59])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f323,f60])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f322,f61])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f321,f62])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f320,f64])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f319,f65])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f318,f66])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f317,f67])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f316,f68])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f315,f71])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f314,f72])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f313,f113])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f310,f106])).

fof(f106,plain,
    ( ~ r1_tmap_1(sK5,sK2,sK6,sK7)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f310,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK5,sK2,sK6,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f291,f114])).

fof(f114,plain,
    ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f109,f74])).

fof(f109,plain,
    ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f291,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f97,f84])).

fof(f97,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X0,X4,X6)
                                      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
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
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f268,plain,
    ( ~ spl9_11
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f267,f144,f125,f207])).

fof(f125,plain,
    ( spl9_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f144,plain,
    ( spl9_6
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f267,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f261,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f261,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f260,f62])).

fof(f260,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f254,f146])).

fof(f146,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f254,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f252,f113])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
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
    inference(resolution,[],[f214,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_connsp_2(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f92,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f148,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f135,f144])).

fof(f135,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f134,f60])).

fof(f134,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f131,f61])).

fof(f131,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f129,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f118,f125])).

fof(f118,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f115,f61])).

fof(f115,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f77,f63])).

fof(f77,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f112,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f75,f108,f104])).

fof(f75,plain,
    ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | r1_tmap_1(sK5,sK2,sK6,sK7) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f76,f108,f104])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | ~ r1_tmap_1(sK5,sK2,sK6,sK7) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (32537)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (32535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (32538)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (32540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (32556)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (32554)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (32536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (32547)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (32545)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (32539)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (32551)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (32536)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (32546)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (32532)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (32553)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (32544)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (32539)Refutation not found, incomplete strategy% (32539)------------------------------
% 0.21/0.51  % (32539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32539)Memory used [KB]: 1791
% 0.21/0.51  % (32539)Time elapsed: 0.064 s
% 0.21/0.51  % (32539)------------------------------
% 0.21/0.51  % (32539)------------------------------
% 0.21/0.51  % (32542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (32548)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (32558)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (32534)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (32532)Refutation not found, incomplete strategy% (32532)------------------------------
% 0.21/0.52  % (32532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32532)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32532)Memory used [KB]: 10746
% 0.21/0.52  % (32532)Time elapsed: 0.104 s
% 0.21/0.52  % (32532)------------------------------
% 0.21/0.52  % (32532)------------------------------
% 0.21/0.52  % (32557)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.26/0.52  % (32555)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f383,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f111,f112,f129,f148,f268,f345,f349,f357,f382])).
% 1.26/0.53  fof(f382,plain,(
% 1.26/0.53    ~spl9_1 | spl9_2),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f381])).
% 1.26/0.53  fof(f381,plain,(
% 1.26/0.53    $false | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f380,f59])).
% 1.26/0.53  fof(f59,plain,(
% 1.26/0.53    ~v2_struct_0(sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f48,plain,(
% 1.26/0.53    (((((((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f40,f47,f46,f45,f44,f43,f42,f41])).
% 1.26/0.53  fof(f41,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f42,plain,(
% 1.26/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK3) & v1_tsep_1(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f43,plain,(
% 1.26/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK3) & v1_tsep_1(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f44,plain,(
% 1.26/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | ~r1_tmap_1(sK5,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | r1_tmap_1(sK5,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | ~r1_tmap_1(sK5,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | r1_tmap_1(sK5,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(sK6))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f46,plain,(
% 1.26/0.53    ? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f47,plain,(
% 1.26/0.53    ? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f40,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f39])).
% 1.26/0.53  fof(f39,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.26/0.53    inference(nnf_transformation,[],[f16])).
% 1.26/0.53  fof(f16,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f15])).
% 1.26/0.53  % (32543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.26/0.53  fof(f15,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f14])).
% 1.26/0.53  fof(f14,negated_conjecture,(
% 1.26/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.26/0.53    inference(negated_conjecture,[],[f13])).
% 1.26/0.53  fof(f13,conjecture,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 1.26/0.53  fof(f380,plain,(
% 1.26/0.53    v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f379,f60])).
% 1.26/0.53  fof(f60,plain,(
% 1.26/0.53    v2_pre_topc(sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f379,plain,(
% 1.26/0.53    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f378,f61])).
% 1.26/0.53  fof(f61,plain,(
% 1.26/0.53    l1_pre_topc(sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f378,plain,(
% 1.26/0.53    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f377,f56])).
% 1.26/0.53  fof(f56,plain,(
% 1.26/0.53    ~v2_struct_0(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f377,plain,(
% 1.26/0.53    v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f376,f57])).
% 1.26/0.53  fof(f57,plain,(
% 1.26/0.53    v2_pre_topc(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f376,plain,(
% 1.26/0.53    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f375,f58])).
% 1.26/0.53  fof(f58,plain,(
% 1.26/0.53    l1_pre_topc(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f375,plain,(
% 1.26/0.53    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f374,f64])).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    ~v2_struct_0(sK5)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f374,plain,(
% 1.26/0.53    v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f373,f65])).
% 1.26/0.53  fof(f65,plain,(
% 1.26/0.53    m1_pre_topc(sK5,sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f373,plain,(
% 1.26/0.53    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f372,f62])).
% 1.26/0.53  fof(f62,plain,(
% 1.26/0.53    ~v2_struct_0(sK4)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f372,plain,(
% 1.26/0.53    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f371,f66])).
% 1.26/0.53  % (32541)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.26/0.53  fof(f66,plain,(
% 1.26/0.53    v1_funct_1(sK6)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f371,plain,(
% 1.26/0.53    ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f370,f67])).
% 1.26/0.53  fof(f67,plain,(
% 1.26/0.53    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f370,plain,(
% 1.26/0.53    ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f369,f68])).
% 1.26/0.53  fof(f68,plain,(
% 1.26/0.53    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f369,plain,(
% 1.26/0.53    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f368,f72])).
% 1.26/0.53  fof(f72,plain,(
% 1.26/0.53    m1_subset_1(sK7,u1_struct_0(sK5))),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f368,plain,(
% 1.26/0.53    ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f367,f113])).
% 1.26/0.53  fof(f113,plain,(
% 1.26/0.53    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.26/0.53    inference(forward_demodulation,[],[f73,f74])).
% 1.26/0.53  fof(f74,plain,(
% 1.26/0.53    sK7 = sK8),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f73,plain,(
% 1.26/0.53    m1_subset_1(sK8,u1_struct_0(sK4))),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f367,plain,(
% 1.26/0.53    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f366,f71])).
% 1.26/0.53  fof(f71,plain,(
% 1.26/0.53    m1_pre_topc(sK4,sK5)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f366,plain,(
% 1.26/0.53    ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f365,f105])).
% 1.26/0.53  fof(f105,plain,(
% 1.26/0.53    r1_tmap_1(sK5,sK2,sK6,sK7) | ~spl9_1),
% 1.26/0.53    inference(avatar_component_clause,[],[f104])).
% 1.26/0.53  fof(f104,plain,(
% 1.26/0.53    spl9_1 <=> r1_tmap_1(sK5,sK2,sK6,sK7)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.26/0.53  fof(f365,plain,(
% 1.26/0.53    ~r1_tmap_1(sK5,sK2,sK6,sK7) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl9_2),
% 1.26/0.53    inference(resolution,[],[f358,f249])).
% 1.26/0.53  fof(f249,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(subsumption_resolution,[],[f99,f84])).
% 1.26/0.53  fof(f84,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.26/0.53    inference(flattening,[],[f27])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f10])).
% 1.26/0.53  fof(f10,axiom,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.26/0.53  fof(f99,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(equality_resolution,[],[f82])).
% 1.26/0.53  fof(f82,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f24])).
% 1.26/0.53  fof(f24,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f23])).
% 1.26/0.53  fof(f23,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f11])).
% 1.26/0.53  fof(f11,axiom,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 1.26/0.53  fof(f358,plain,(
% 1.26/0.53    ~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7) | spl9_2),
% 1.26/0.53    inference(forward_demodulation,[],[f110,f74])).
% 1.26/0.53  fof(f110,plain,(
% 1.26/0.53    ~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | spl9_2),
% 1.26/0.53    inference(avatar_component_clause,[],[f108])).
% 1.26/0.53  fof(f108,plain,(
% 1.26/0.53    spl9_2 <=> r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.26/0.53  fof(f357,plain,(
% 1.26/0.53    spl9_14),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f356])).
% 1.26/0.53  fof(f356,plain,(
% 1.26/0.53    $false | spl9_14),
% 1.26/0.53    inference(subsumption_resolution,[],[f355,f69])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    v1_tsep_1(sK4,sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f355,plain,(
% 1.26/0.53    ~v1_tsep_1(sK4,sK3) | spl9_14),
% 1.26/0.53    inference(subsumption_resolution,[],[f354,f63])).
% 1.26/0.53  fof(f63,plain,(
% 1.26/0.53    m1_pre_topc(sK4,sK3)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f354,plain,(
% 1.26/0.53    ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3) | spl9_14),
% 1.26/0.53    inference(resolution,[],[f353,f89])).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f53])).
% 1.26/0.53  fof(f53,plain,(
% 1.26/0.53    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 1.26/0.53    inference(flattening,[],[f52])).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 1.26/0.53    inference(nnf_transformation,[],[f36])).
% 1.26/0.53  fof(f36,plain,(
% 1.26/0.53    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 1.26/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.26/0.53  fof(f353,plain,(
% 1.26/0.53    ~sP0(sK3,sK4) | spl9_14),
% 1.26/0.53    inference(subsumption_resolution,[],[f352,f61])).
% 1.26/0.53  fof(f352,plain,(
% 1.26/0.53    ~sP0(sK3,sK4) | ~l1_pre_topc(sK3) | spl9_14),
% 1.26/0.53    inference(subsumption_resolution,[],[f351,f60])).
% 1.26/0.53  fof(f351,plain,(
% 1.26/0.53    ~v2_pre_topc(sK3) | ~sP0(sK3,sK4) | ~l1_pre_topc(sK3) | spl9_14),
% 1.26/0.53    inference(resolution,[],[f344,f232])).
% 1.26/0.53  fof(f232,plain,(
% 1.26/0.53    ( ! [X2,X3] : (v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3) | ~sP0(X3,X2) | ~l1_pre_topc(X3)) )),
% 1.26/0.53    inference(subsumption_resolution,[],[f231,f88])).
% 1.26/0.53  fof(f88,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | m1_pre_topc(X1,X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f53])).
% 1.26/0.53  fof(f231,plain,(
% 1.26/0.53    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~sP0(X3,X2) | v3_pre_topc(u1_struct_0(X2),X3)) )),
% 1.26/0.53    inference(resolution,[],[f229,f85])).
% 1.26/0.53  fof(f85,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X0,X2) | v3_pre_topc(X1,X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f51])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 1.26/0.53    inference(rectify,[],[f50])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 1.26/0.53    inference(nnf_transformation,[],[f37])).
% 1.26/0.53  fof(f37,plain,(
% 1.26/0.53    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 1.26/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.26/0.53  fof(f229,plain,(
% 1.26/0.53    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.26/0.53    inference(subsumption_resolution,[],[f100,f78])).
% 1.26/0.53  fof(f78,plain,(
% 1.26/0.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,axiom,(
% 1.26/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.26/0.53  fof(f100,plain,(
% 1.26/0.53    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.26/0.53    inference(equality_resolution,[],[f90])).
% 1.26/0.53  fof(f90,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f38])).
% 1.26/0.53  fof(f38,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.26/0.53    inference(definition_folding,[],[f30,f37,f36])).
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.26/0.53    inference(flattening,[],[f29])).
% 1.26/0.53  fof(f29,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,axiom,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.26/0.53  fof(f344,plain,(
% 1.26/0.53    ~v3_pre_topc(u1_struct_0(sK4),sK3) | spl9_14),
% 1.26/0.53    inference(avatar_component_clause,[],[f342])).
% 1.26/0.53  fof(f342,plain,(
% 1.26/0.53    spl9_14 <=> v3_pre_topc(u1_struct_0(sK4),sK3)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.26/0.53  fof(f349,plain,(
% 1.26/0.53    spl9_11 | spl9_13),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f348])).
% 1.26/0.53  fof(f348,plain,(
% 1.26/0.53    $false | (spl9_11 | spl9_13)),
% 1.26/0.53    inference(subsumption_resolution,[],[f347,f113])).
% 1.26/0.53  fof(f347,plain,(
% 1.26/0.53    ~m1_subset_1(sK7,u1_struct_0(sK4)) | (spl9_11 | spl9_13)),
% 1.26/0.53    inference(subsumption_resolution,[],[f346,f208])).
% 1.26/0.53  fof(f208,plain,(
% 1.26/0.53    ~v1_xboole_0(u1_struct_0(sK4)) | spl9_11),
% 1.26/0.53    inference(avatar_component_clause,[],[f207])).
% 1.26/0.53  fof(f207,plain,(
% 1.26/0.53    spl9_11 <=> v1_xboole_0(u1_struct_0(sK4))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.26/0.53  fof(f346,plain,(
% 1.26/0.53    v1_xboole_0(u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | spl9_13),
% 1.26/0.53    inference(resolution,[],[f340,f91])).
% 1.26/0.53  fof(f91,plain,(
% 1.26/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f32])).
% 1.26/0.53  fof(f32,plain,(
% 1.26/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.26/0.53    inference(flattening,[],[f31])).
% 1.26/0.53  fof(f31,plain,(
% 1.26/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.26/0.53    inference(ennf_transformation,[],[f2])).
% 1.26/0.53  fof(f2,axiom,(
% 1.26/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.26/0.53  fof(f340,plain,(
% 1.26/0.53    ~r2_hidden(sK7,u1_struct_0(sK4)) | spl9_13),
% 1.26/0.53    inference(avatar_component_clause,[],[f338])).
% 1.26/0.53  fof(f338,plain,(
% 1.26/0.53    spl9_13 <=> r2_hidden(sK7,u1_struct_0(sK4))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.26/0.53  fof(f345,plain,(
% 1.26/0.53    ~spl9_13 | ~spl9_14 | spl9_1 | ~spl9_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f336,f108,f104,f342,f338])).
% 1.26/0.53  fof(f336,plain,(
% 1.26/0.53    ~v3_pre_topc(u1_struct_0(sK4),sK3) | ~r2_hidden(sK7,u1_struct_0(sK4)) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f335,f63])).
% 1.26/0.53  fof(f335,plain,(
% 1.26/0.53    ~v3_pre_topc(u1_struct_0(sK4),sK3) | ~r2_hidden(sK7,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK3) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(resolution,[],[f331,f101])).
% 1.26/0.53  fof(f101,plain,(
% 1.26/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.26/0.53    inference(equality_resolution,[],[f94])).
% 1.26/0.53  fof(f94,plain,(
% 1.26/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.26/0.53    inference(cnf_transformation,[],[f55])).
% 1.26/0.53  fof(f55,plain,(
% 1.26/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.26/0.53    inference(flattening,[],[f54])).
% 1.26/0.53  fof(f54,plain,(
% 1.26/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.26/0.53    inference(nnf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.26/0.53  fof(f331,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~r2_hidden(sK7,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f329,f61])).
% 1.26/0.53  fof(f329,plain,(
% 1.26/0.53    ( ! [X0] : (~r2_hidden(sK7,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(resolution,[],[f328,f78])).
% 1.26/0.53  fof(f328,plain,(
% 1.26/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK4))) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f327,f56])).
% 1.26/0.53  fof(f327,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f326,f57])).
% 1.26/0.53  fof(f326,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f325,f58])).
% 1.26/0.53  fof(f325,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f324,f59])).
% 1.26/0.53  fof(f324,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f323,f60])).
% 1.26/0.53  fof(f323,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f322,f61])).
% 1.26/0.53  fof(f322,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f321,f62])).
% 1.26/0.53  fof(f321,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f320,f64])).
% 1.26/0.53  fof(f320,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f319,f65])).
% 1.26/0.53  fof(f319,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f318,f66])).
% 1.26/0.53  fof(f318,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f317,f67])).
% 1.26/0.53  fof(f317,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f316,f68])).
% 1.26/0.53  fof(f316,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f315,f71])).
% 1.26/0.53  fof(f315,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f314,f72])).
% 1.26/0.53  fof(f314,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f313,f113])).
% 1.26/0.53  fof(f313,plain,(
% 1.26/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f310,f106])).
% 1.26/0.53  fof(f106,plain,(
% 1.26/0.53    ~r1_tmap_1(sK5,sK2,sK6,sK7) | spl9_1),
% 1.26/0.53    inference(avatar_component_clause,[],[f104])).
% 1.26/0.53  fof(f310,plain,(
% 1.26/0.53    ( ! [X0] : (r1_tmap_1(sK5,sK2,sK6,sK7) | ~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_2),
% 1.26/0.53    inference(resolution,[],[f291,f114])).
% 1.26/0.53  fof(f114,plain,(
% 1.26/0.53    r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7) | ~spl9_2),
% 1.26/0.53    inference(forward_demodulation,[],[f109,f74])).
% 1.26/0.53  fof(f109,plain,(
% 1.26/0.53    r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~spl9_2),
% 1.26/0.53    inference(avatar_component_clause,[],[f108])).
% 1.26/0.53  fof(f291,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(subsumption_resolution,[],[f97,f84])).
% 1.26/0.53  fof(f97,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X7) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(equality_resolution,[],[f81])).
% 1.26/0.53  fof(f81,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.53    inference(nnf_transformation,[],[f22])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f21])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f12])).
% 1.26/0.53  fof(f12,axiom,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 1.26/0.53  fof(f268,plain,(
% 1.26/0.53    ~spl9_11 | ~spl9_4 | ~spl9_6),
% 1.26/0.53    inference(avatar_split_clause,[],[f267,f144,f125,f207])).
% 1.26/0.53  fof(f125,plain,(
% 1.26/0.53    spl9_4 <=> l1_pre_topc(sK4)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.26/0.53  fof(f144,plain,(
% 1.26/0.53    spl9_6 <=> v2_pre_topc(sK4)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.26/0.53  fof(f267,plain,(
% 1.26/0.53    ~v1_xboole_0(u1_struct_0(sK4)) | (~spl9_4 | ~spl9_6)),
% 1.26/0.53    inference(subsumption_resolution,[],[f261,f127])).
% 1.26/0.53  fof(f127,plain,(
% 1.26/0.53    l1_pre_topc(sK4) | ~spl9_4),
% 1.26/0.53    inference(avatar_component_clause,[],[f125])).
% 1.26/0.53  fof(f261,plain,(
% 1.26/0.53    ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~spl9_6),
% 1.26/0.53    inference(subsumption_resolution,[],[f260,f62])).
% 1.26/0.53  fof(f260,plain,(
% 1.26/0.53    v2_struct_0(sK4) | ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~spl9_6),
% 1.26/0.53    inference(subsumption_resolution,[],[f254,f146])).
% 1.26/0.53  fof(f146,plain,(
% 1.26/0.53    v2_pre_topc(sK4) | ~spl9_6),
% 1.26/0.53    inference(avatar_component_clause,[],[f144])).
% 1.26/0.53  fof(f254,plain,(
% 1.26/0.53    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4)),
% 1.26/0.53    inference(resolution,[],[f252,f113])).
% 1.26/0.53  fof(f252,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.26/0.53    inference(duplicate_literal_removal,[],[f250])).
% 1.26/0.53  fof(f250,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(resolution,[],[f214,f79])).
% 1.26/0.53  fof(f79,plain,(
% 1.26/0.53    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f20])).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f19])).
% 1.26/0.53  fof(f19,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f7])).
% 1.26/0.53  fof(f7,axiom,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 1.26/0.53  fof(f214,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_connsp_2(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.26/0.53    inference(resolution,[],[f92,f96])).
% 1.26/0.53  fof(f96,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f35])).
% 1.26/0.53  fof(f35,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.26/0.53    inference(ennf_transformation,[],[f3])).
% 1.26/0.53  fof(f3,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.26/0.53  fof(f92,plain,(
% 1.26/0.53    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f34,plain,(
% 1.26/0.53    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f33])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f6])).
% 1.26/0.53  fof(f6,axiom,(
% 1.26/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 1.26/0.53  fof(f148,plain,(
% 1.26/0.53    spl9_6),
% 1.26/0.53    inference(avatar_split_clause,[],[f135,f144])).
% 1.26/0.53  fof(f135,plain,(
% 1.26/0.53    v2_pre_topc(sK4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f134,f60])).
% 1.26/0.53  fof(f134,plain,(
% 1.26/0.53    v2_pre_topc(sK4) | ~v2_pre_topc(sK3)),
% 1.26/0.53    inference(subsumption_resolution,[],[f131,f61])).
% 1.26/0.53  fof(f131,plain,(
% 1.26/0.53    v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.26/0.53    inference(resolution,[],[f83,f63])).
% 1.26/0.53  fof(f83,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f26])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.26/0.53    inference(flattening,[],[f25])).
% 1.26/0.53  fof(f25,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f4])).
% 1.26/0.53  fof(f4,axiom,(
% 1.26/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.26/0.53  fof(f129,plain,(
% 1.26/0.53    spl9_4),
% 1.26/0.53    inference(avatar_split_clause,[],[f118,f125])).
% 1.26/0.53  fof(f118,plain,(
% 1.26/0.53    l1_pre_topc(sK4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f115,f61])).
% 1.26/0.53  fof(f115,plain,(
% 1.26/0.53    l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 1.26/0.53    inference(resolution,[],[f77,f63])).
% 1.26/0.53  fof(f77,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f17])).
% 1.26/0.53  fof(f17,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f5])).
% 1.26/0.53  fof(f5,axiom,(
% 1.26/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.26/0.53  fof(f112,plain,(
% 1.26/0.53    spl9_1 | spl9_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f75,f108,f104])).
% 1.26/0.53  fof(f75,plain,(
% 1.26/0.53    r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK2,sK6,sK7)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  fof(f111,plain,(
% 1.26/0.53    ~spl9_1 | ~spl9_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f76,f108,f104])).
% 1.26/0.53  fof(f76,plain,(
% 1.26/0.53    ~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK2,sK6,sK7)),
% 1.26/0.53    inference(cnf_transformation,[],[f48])).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (32536)------------------------------
% 1.26/0.53  % (32536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (32536)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (32536)Memory used [KB]: 6396
% 1.26/0.53  % (32536)Time elapsed: 0.095 s
% 1.26/0.53  % (32536)------------------------------
% 1.26/0.53  % (32536)------------------------------
% 1.26/0.53  % (32528)Success in time 0.168 s
%------------------------------------------------------------------------------

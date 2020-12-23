%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  199 (1753 expanded)
%              Number of leaves         :   29 ( 838 expanded)
%              Depth                    :   39
%              Number of atoms          : 1351 (36662 expanded)
%              Number of equality atoms :   62 (2154 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f111,f309,f314,f333,f336,f352,f378])).

fof(f378,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f376,f354])).

fof(f354,plain,
    ( ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | spl8_2 ),
    inference(forward_demodulation,[],[f353,f318])).

fof(f318,plain,(
    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(forward_demodulation,[],[f317,f271])).

fof(f271,plain,(
    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f191,f75])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK2,sK1)
    & v1_tsep_1(sK2,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f48,f55,f54,f53,f52,f51,f50,f49])).

fof(f49,plain,
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
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK0,X4,X5) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK0,X4,X5) )
                            & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,X1)
                    & v1_tsep_1(X2,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
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
                          ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK0,X4,X5) )
                          & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,sK1)
                  & v1_tsep_1(X2,sK1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK0,X4,X5) )
                        & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X2,sK1)
                & v1_tsep_1(X2,sK1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                        | ~ r1_tmap_1(X3,sK0,X4,X5) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                        | r1_tmap_1(X3,sK0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(sK2,sK1)
              & v1_tsep_1(sK2,sK1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                      | ~ r1_tmap_1(X3,sK0,X4,X5) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                      | r1_tmap_1(X3,sK0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(sK2,sK1)
            & v1_tsep_1(sK2,sK1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                    | ~ r1_tmap_1(sK3,sK0,X4,X5) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                    | r1_tmap_1(sK3,sK0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & m1_pre_topc(sK2,sK1)
          & v1_tsep_1(sK2,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                  | ~ r1_tmap_1(sK3,sK0,X4,X5) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                  | r1_tmap_1(sK3,sK0,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
                | ~ r1_tmap_1(sK3,sK0,sK4,X5) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
                | r1_tmap_1(sK3,sK0,sK4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK2,sK1)
      & v1_tsep_1(sK2,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
              | ~ r1_tmap_1(sK3,sK0,sK4,X5) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
              | r1_tmap_1(sK3,sK0,sK4,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
            | r1_tmap_1(sK3,sK0,sK4,sK5) )
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
          | r1_tmap_1(sK3,sK0,sK4,sK5) )
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
        | r1_tmap_1(sK3,sK0,sK4,sK5) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f191,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f190,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f190,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f189,f119])).

fof(f119,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f118,f64])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f115,f65])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f115,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f69,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f69,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f189,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f188,f121])).

fof(f121,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f117,f65])).

fof(f117,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f188,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f187,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f187,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f186,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f186,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f185,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f185,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f184,f70])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f184,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f172,f71])).

fof(f71,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f172,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f72,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f317,plain,(
    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f291,f75])).

fof(f291,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f290,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f290,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f289,f64])).

fof(f289,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f288,f65])).

fof(f288,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f197,f69])).

fof(f197,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(sK3,X6)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,sK3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f196,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f196,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f195,f60])).

fof(f195,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f194,f61])).

fof(f194,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f193,f62])).

fof(f193,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f192,f70])).

fof(f192,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f173,f71])).

fof(f173,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f353,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl8_2 ),
    inference(forward_demodulation,[],[f109,f78])).

fof(f78,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f376,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f375,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f375,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f360,f75])).

fof(f360,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl8_1 ),
    inference(resolution,[],[f356,f112])).

fof(f112,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f77,f78])).

fof(f77,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f355,f76])).

fof(f76,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) )
    | ~ spl8_1 ),
    inference(resolution,[],[f104,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) ) ),
    inference(subsumption_resolution,[],[f182,f60])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f61])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f62])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f68])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f119])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f121])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f70])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f71])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f101])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f104,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f352,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f304,f350])).

fof(f350,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f349,f60])).

fof(f349,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f348,f61])).

fof(f348,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f347,f62])).

fof(f347,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f346,f68])).

fof(f346,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f345,f119])).

fof(f345,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f344,f121])).

fof(f344,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f343,f70])).

fof(f343,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f342,f71])).

fof(f342,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f341,f72])).

fof(f341,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f340,f66])).

fof(f340,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f339,f75])).

fof(f339,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f338,f76])).

fof(f338,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f337,f112])).

fof(f337,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f320,f105])).

fof(f105,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f320,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f319,f99])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f319,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f113,f318])).

fof(f113,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f108,f78])).

fof(f108,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f304,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl8_20
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f336,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f335,f307,f302,f299])).

fof(f299,plain,
    ( spl8_19
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f307,plain,
    ( spl8_21
  <=> ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK2))
        | r2_hidden(X2,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f335,plain,
    ( ! [X0] :
        ( v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f334,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f75,f94])).

fof(f334,plain,
    ( ! [X0] :
        ( v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f323,f68])).

fof(f323,plain,
    ( ! [X0] :
        ( v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_21 ),
    inference(resolution,[],[f322,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
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
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f322,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_21 ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_21 ),
    inference(resolution,[],[f315,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

% (16286)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,u1_struct_0(sK3)),u1_struct_0(sK2))
        | r1_tarski(X0,u1_struct_0(sK3)) )
    | ~ spl8_21 ),
    inference(resolution,[],[f308,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f308,plain,
    ( ! [X2] :
        ( r2_hidden(X2,u1_struct_0(sK3))
        | ~ r2_hidden(X2,u1_struct_0(sK2)) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f307])).

fof(f333,plain,(
    ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f331,f69])).

fof(f331,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f330,f65])).

fof(f330,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f329,f64])).

fof(f329,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f328,f63])).

fof(f328,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_19 ),
    inference(resolution,[],[f300,f73])).

fof(f73,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK2,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f299])).

fof(f314,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f312,f121])).

fof(f312,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f311,f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f311,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f310,f68])).

fof(f310,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f145,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_4
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f309,plain,
    ( spl8_4
    | spl8_21 ),
    inference(avatar_split_clause,[],[f242,f307,f143])).

fof(f242,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK3))
      | r2_hidden(X2,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f210,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f210,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f134,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f134,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f132,f121])).

fof(f132,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f75,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f111,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f79,f107,f103])).

fof(f79,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

% (16268)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f110,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f80,f107,f103])).

fof(f80,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (16265)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (16273)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (16281)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (16264)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (16265)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (16260)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (16258)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (16272)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (16259)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16261)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (16263)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (16276)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (16280)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f110,f111,f309,f314,f333,f336,f352,f378])).
% 0.20/0.52  fof(f378,plain,(
% 0.20/0.52    ~spl8_1 | spl8_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f377])).
% 0.20/0.52  fof(f377,plain,(
% 0.20/0.52    $false | (~spl8_1 | spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f376,f354])).
% 0.20/0.52  fof(f354,plain,(
% 0.20/0.52    ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | spl8_2),
% 0.20/0.52    inference(forward_demodulation,[],[f353,f318])).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f317,f271])).
% 0.20/0.52  fof(f271,plain,(
% 0.20/0.52    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f191,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f48,f55,f54,f53,f52,f51,f50,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f16])).
% 0.20/0.52  fof(f16,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f190,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ~v2_struct_0(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f119])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    v2_pre_topc(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f118,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    v2_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    v2_pre_topc(sK3) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f115,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    l1_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    v2_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f69,f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f188,f121])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    l1_pre_topc(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f117,f65])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f69,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f187,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | v2_struct_0(sK0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f186,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f185,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f184,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f172,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK0,sK4,X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X4)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.52    inference(resolution,[],[f72,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f317,plain,(
% 0.20/0.52    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f291,f75])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f290,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f290,plain,(
% 0.20/0.52    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f289,f64])).
% 0.20/0.52  fof(f289,plain,(
% 0.20/0.52    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f288,f65])).
% 0.20/0.52  fof(f288,plain,(
% 0.20/0.52    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f197,f69])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(sK3,X6) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~m1_pre_topc(X5,sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f196,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f195,f60])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f194,f61])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f193,f62])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f192,f70])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f173,f71])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK0,sK3,X5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X5)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.52    inference(resolution,[],[f72,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.52  fof(f353,plain,(
% 0.20/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl8_2),
% 0.20/0.52    inference(forward_demodulation,[],[f109,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    sK5 = sK6),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    spl8_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~spl8_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f375,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~v2_struct_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    v2_struct_0(sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~spl8_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f360,f75])).
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~spl8_1),
% 0.20/0.52    inference(resolution,[],[f356,f112])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f77,f78])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f356,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)) ) | ~spl8_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f355,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f355,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)) ) | ~spl8_1),
% 0.20/0.52    inference(resolution,[],[f104,f183])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f182,f60])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f181,f61])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f62])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f179,f68])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f178,f119])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f177,f121])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f176,f70])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f170,f71])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f72,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl8_1 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    spl8_1 | ~spl8_2 | ~spl8_20),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f351])).
% 0.20/0.52  fof(f351,plain,(
% 0.20/0.52    $false | (spl8_1 | ~spl8_2 | ~spl8_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f304,f350])).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f349,f60])).
% 0.20/0.52  fof(f349,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f348,f61])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f347,f62])).
% 0.20/0.52  fof(f347,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f346,f68])).
% 0.20/0.52  fof(f346,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f345,f119])).
% 0.20/0.52  fof(f345,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f344,f121])).
% 0.20/0.52  fof(f344,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f343,f70])).
% 0.20/0.52  fof(f343,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f342,f71])).
% 0.20/0.52  fof(f342,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f341,f72])).
% 0.20/0.52  fof(f341,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f340,f66])).
% 0.20/0.52  fof(f340,plain,(
% 0.20/0.52    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f339,f75])).
% 0.20/0.52  fof(f339,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f338,f76])).
% 0.20/0.52  fof(f338,plain,(
% 0.20/0.52    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f337,f112])).
% 0.20/0.52  fof(f337,plain,(
% 0.20/0.52    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f320,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f320,plain,(
% 0.20/0.52    r1_tmap_1(sK3,sK0,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_2),
% 0.20/0.52    inference(resolution,[],[f319,f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.20/0.52  fof(f319,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~spl8_2),
% 0.20/0.52    inference(backward_demodulation,[],[f113,f318])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~spl8_2),
% 0.20/0.52    inference(forward_demodulation,[],[f108,f78])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f107])).
% 0.20/0.52  fof(f304,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK3) | ~spl8_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f302])).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    spl8_20 <=> v1_tsep_1(sK2,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    spl8_19 | spl8_20 | ~spl8_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f335,f307,f302,f299])).
% 0.20/0.52  fof(f299,plain,(
% 0.20/0.52    spl8_19 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.52  fof(f307,plain,(
% 0.20/0.52    spl8_21 <=> ! [X2] : (~r2_hidden(X2,u1_struct_0(sK2)) | r2_hidden(X2,u1_struct_0(sK3)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.20/0.52  fof(f335,plain,(
% 0.20/0.52    ( ! [X0] : (v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_21),
% 0.20/0.52    inference(subsumption_resolution,[],[f334,f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(sK3,X0) | m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(resolution,[],[f75,f94])).
% 0.20/0.52  fof(f334,plain,(
% 0.20/0.52    ( ! [X0] : (v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_21),
% 0.20/0.52    inference(subsumption_resolution,[],[f323,f68])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    ( ! [X0] : (v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_21),
% 0.20/0.52    inference(resolution,[],[f322,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.20/0.52  fof(f322,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl8_21),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f321])).
% 0.20/0.52  fof(f321,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl8_21),
% 0.20/0.52    inference(resolution,[],[f315,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f59])).
% 0.20/0.52  % (16286)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK7(X0,u1_struct_0(sK3)),u1_struct_0(sK2)) | r1_tarski(X0,u1_struct_0(sK3))) ) | ~spl8_21),
% 0.20/0.52    inference(resolution,[],[f308,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f59])).
% 0.20/0.52  fof(f308,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(X2,u1_struct_0(sK3)) | ~r2_hidden(X2,u1_struct_0(sK2))) ) | ~spl8_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f307])).
% 0.20/0.52  fof(f333,plain,(
% 0.20/0.52    ~spl8_19),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f332])).
% 0.20/0.52  fof(f332,plain,(
% 0.20/0.52    $false | ~spl8_19),
% 0.20/0.52    inference(subsumption_resolution,[],[f331,f69])).
% 0.20/0.52  fof(f331,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK1) | ~spl8_19),
% 0.20/0.52    inference(subsumption_resolution,[],[f330,f65])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | ~spl8_19),
% 0.20/0.52    inference(subsumption_resolution,[],[f329,f64])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | ~spl8_19),
% 0.20/0.52    inference(subsumption_resolution,[],[f328,f63])).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | ~spl8_19),
% 0.20/0.52    inference(resolution,[],[f300,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    v1_tsep_1(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f300,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_tsep_1(sK2,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0)) ) | ~spl8_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f299])).
% 0.20/0.52  fof(f314,plain,(
% 0.20/0.52    ~spl8_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f313])).
% 0.20/0.52  fof(f313,plain,(
% 0.20/0.52    $false | ~spl8_4),
% 0.20/0.52    inference(subsumption_resolution,[],[f312,f121])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    ~l1_pre_topc(sK3) | ~spl8_4),
% 0.20/0.52    inference(resolution,[],[f311,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    ~l1_struct_0(sK3) | ~spl8_4),
% 0.20/0.52    inference(subsumption_resolution,[],[f310,f68])).
% 0.20/0.52  fof(f310,plain,(
% 0.20/0.52    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl8_4),
% 0.20/0.52    inference(resolution,[],[f145,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK3)) | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    spl8_4 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f309,plain,(
% 0.20/0.52    spl8_4 | spl8_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f242,f307,f143])).
% 0.20/0.52  fof(f242,plain,(
% 0.20/0.52    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK3)) | r2_hidden(X2,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(resolution,[],[f210,f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK2))) )),
% 0.20/0.52    inference(resolution,[],[f134,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f121])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 0.20/0.52    inference(resolution,[],[f75,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl8_1 | spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f79,f107,f103])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  % (16268)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f80,f107,f103])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (16265)------------------------------
% 0.20/0.52  % (16265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16265)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (16265)Memory used [KB]: 11001
% 0.20/0.52  % (16265)Time elapsed: 0.111 s
% 0.20/0.52  % (16265)------------------------------
% 0.20/0.52  % (16265)------------------------------
% 0.20/0.52  % (16278)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (16256)Success in time 0.169 s
%------------------------------------------------------------------------------

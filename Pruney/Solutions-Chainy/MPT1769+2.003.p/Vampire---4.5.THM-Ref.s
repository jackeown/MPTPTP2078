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
% DateTime   : Thu Dec  3 13:18:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  295 (5532 expanded)
%              Number of leaves         :   28 (2656 expanded)
%              Depth                    :   52
%              Number of atoms          : 1906 (133770 expanded)
%              Number of equality atoms :  101 (7126 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1879,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f112,f285,f289,f564,f1584,f1602,f1795,f1877])).

fof(f1877,plain,
    ( spl7_2
    | ~ spl7_64 ),
    inference(avatar_contradiction_clause,[],[f1876])).

fof(f1876,plain,
    ( $false
    | spl7_2
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1861,f216])).

fof(f216,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    inference(subsumption_resolution,[],[f215,f69])).

fof(f69,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
    & sK0 = sK3
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f45,f52,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                            & sK0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                          & sK0 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5)
                          | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5) )
                        & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                        & sK0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                      & sK0 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5) )
                    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                    & sK0 = X3
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                  & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                  & sK0 = sK3
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
                  & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                  | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5)
                  | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
                & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                & sK0 = sK3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
                & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
                | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
              & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
                | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
              & sK0 = sK3
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
              | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
            & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5)
              | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5) )
            & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
            & sK0 = sK3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X6) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
            | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
          & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
            | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
          & sK0 = sK3
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X6) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X6] :
        ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
          | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
        & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
          | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5) )
        & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
        & sK0 = sK3
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X6) )
   => ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
      & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
      & sK0 = sK3
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f215,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f176,f70])).

fof(f70,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f176,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f71,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
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

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1861,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)
    | spl7_2
    | ~ spl7_64 ),
    inference(backward_demodulation,[],[f1633,f1849])).

fof(f1849,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1848,f69])).

fof(f1848,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1847,f70])).

fof(f1847,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1846,f71])).

fof(f1846,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl7_64 ),
    inference(resolution,[],[f1844,f1659])).

fof(f1659,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X7,k7_relat_1(sK4,u1_struct_0(sK2)))
      | k7_relat_1(sK4,u1_struct_0(sK2)) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f1658,f418])).

fof(f418,plain,(
    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f417,f113])).

fof(f113,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f58,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f417,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f416,f114])).

fof(f114,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f61,f79])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f416,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f415,f66])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f415,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f414,f67])).

fof(f67,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f414,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f413,f68])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f413,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f409,f118])).

fof(f118,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f117,f79])).

fof(f117,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f116,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f63,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f409,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f89,f381])).

fof(f381,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f378,f63])).

fof(f378,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k7_relat_1(sK4,u1_struct_0(X6)) ) ),
    inference(forward_demodulation,[],[f163,f164])).

fof(f164,plain,(
    ! [X7] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X7) = k7_relat_1(sK4,X7) ),
    inference(subsumption_resolution,[],[f133,f66])).

fof(f133,plain,(
    ! [X7] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X7) = k7_relat_1(sK4,X7)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f68,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f163,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f162,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f162,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f161,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f58])).

fof(f160,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f159,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f158,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f61])).

fof(f157,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f66])).

fof(f156,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f67])).

fof(f132,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(X6,sK0)
      | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f1658,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X7,k7_relat_1(sK4,u1_struct_0(sK2)))
      | k7_relat_1(sK4,u1_struct_0(sK2)) = X7
      | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f1642,f118])).

fof(f1642,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X7,k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ l1_struct_0(sK2)
      | k7_relat_1(sK4,u1_struct_0(sK2)) = X7
      | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X7) ) ),
    inference(superposition,[],[f338,f381])).

fof(f338,plain,(
    ! [X14,X15] :
      ( ~ r2_funct_2(u1_struct_0(X14),u1_struct_0(sK1),X15,k2_tmap_1(sK0,sK1,sK4,X14))
      | ~ l1_struct_0(X14)
      | k2_tmap_1(sK0,sK1,sK4,X14) = X15
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X14),u1_struct_0(X14),u1_struct_0(sK1))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1))))
      | ~ v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1))
      | ~ v1_funct_1(X15) ) ),
    inference(subsumption_resolution,[],[f315,f151])).

fof(f151,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4)) ) ),
    inference(subsumption_resolution,[],[f150,f113])).

fof(f150,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f114])).

fof(f149,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4))
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f66])).

fof(f148,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f67])).

fof(f130,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f315,plain,(
    ! [X14,X15] :
      ( ~ l1_struct_0(X14)
      | ~ r2_funct_2(u1_struct_0(X14),u1_struct_0(sK1),X15,k2_tmap_1(sK0,sK1,sK4,X14))
      | k2_tmap_1(sK0,sK1,sK4,X14) = X15
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X14),u1_struct_0(X14),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X14))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1))))
      | ~ v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1))
      | ~ v1_funct_1(X15) ) ),
    inference(resolution,[],[f155,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f155,plain,(
    ! [X5] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ l1_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f154,f113])).

fof(f154,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f114])).

fof(f153,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f66])).

fof(f152,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f67])).

fof(f131,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1844,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1843,f168])).

fof(f168,plain,(
    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) ),
    inference(subsumption_resolution,[],[f167,f66])).

fof(f167,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f135,f67])).

fof(f135,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f68,f101])).

fof(f1843,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f1842,f383])).

fof(f383,plain,(
    sK4 = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(forward_demodulation,[],[f382,f219])).

fof(f219,plain,(
    sK4 = k7_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f218,f137])).

fof(f137,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f68,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f218,plain,
    ( sK4 = k7_relat_1(sK4,u1_struct_0(sK0))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f136,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f136,plain,(
    v4_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(resolution,[],[f68,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f382,plain,(
    k7_relat_1(sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(resolution,[],[f378,f122])).

fof(f122,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(backward_demodulation,[],[f65,f75])).

fof(f75,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f1842,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1841,f56])).

fof(f1841,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | v2_struct_0(sK0)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1840,f122])).

fof(f1840,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1839,f66])).

fof(f1839,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1838,f67])).

fof(f1838,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1837,f68])).

fof(f1837,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1826,f63])).

fof(f1826,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_64 ),
    inference(superposition,[],[f429,f1601])).

fof(f1601,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f1599])).

fof(f1599,plain,
    ( spl7_64
  <=> sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f429,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f428,f56])).

fof(f428,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f427,f57])).

fof(f427,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f426,f58])).

fof(f426,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f425,f59])).

fof(f425,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f424,f60])).

fof(f424,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f423,f61])).

fof(f423,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f422,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f422,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f421,f63])).

fof(f421,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f420,f66])).

fof(f420,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f419,f67])).

fof(f419,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f410,f68])).

fof(f410,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f82,f381])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

fof(f1633,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | spl7_2 ),
    inference(backward_demodulation,[],[f110,f381])).

fof(f110,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_2
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1795,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_63 ),
    inference(avatar_contradiction_clause,[],[f1794])).

fof(f1794,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | spl7_63 ),
    inference(subsumption_resolution,[],[f1597,f1629])).

fof(f1629,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f1628,f75])).

fof(f1628,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f105,f284])).

fof(f284,plain,
    ( sK4 = sK6
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl7_6
  <=> sK4 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f105,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_1
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1597,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | spl7_63 ),
    inference(avatar_component_clause,[],[f1595])).

fof(f1595,plain,
    ( spl7_63
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f1602,plain,
    ( ~ spl7_63
    | spl7_64
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f1593,f508,f1599,f1595])).

fof(f508,plain,
    ( spl7_7
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1593,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f1592,f478])).

fof(f478,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(resolution,[],[f473,f63])).

fof(f473,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) ) ),
    inference(subsumption_resolution,[],[f472,f56])).

fof(f472,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f471,f57])).

fof(f471,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f470,f58])).

fof(f470,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f142,f122])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f141,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f140,f60])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f139,f61])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f67])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f68,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1592,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f674,f509])).

fof(f509,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f508])).

fof(f674,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(resolution,[],[f214,f487])).

fof(f487,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f486,f63])).

fof(f486,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f485,f56])).

fof(f485,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f484,f57])).

fof(f484,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f483,f58])).

fof(f483,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f147,f122])).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(sK0,X2)
      | ~ m1_pre_topc(X3,X2)
      | m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f146,f59])).

fof(f146,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK0,X2)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f145,f60])).

fof(f145,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK0,X2)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f144,f61])).

fof(f144,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK0,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f143,f66])).

fof(f143,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK0,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f129,f67])).

fof(f129,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK0,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f68,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f41])).

fof(f214,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | sK5 = X8
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X8,sK5)
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X8) ) ),
    inference(subsumption_resolution,[],[f213,f69])).

fof(f213,plain,(
    ! [X8] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X8,sK5)
      | sK5 = X8
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X8) ) ),
    inference(subsumption_resolution,[],[f175,f70])).

fof(f175,plain,(
    ! [X8] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X8,sK5)
      | sK5 = X8
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X8) ) ),
    inference(resolution,[],[f71,f91])).

fof(f1584,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f1583])).

fof(f1583,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1582,f168])).

fof(f1582,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f1581,f383])).

fof(f1581,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1580,f56])).

fof(f1580,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | v2_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1579,f122])).

fof(f1579,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1578,f66])).

fof(f1578,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1577,f67])).

fof(f1577,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1576,f68])).

fof(f1576,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1574,f63])).

fof(f1574,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f729,f304])).

fof(f304,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | spl7_1
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f303,f75])).

fof(f303,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl7_1
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f106,f284])).

fof(f106,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f729,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f728,f56])).

fof(f728,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f727,f57])).

fof(f727,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f726,f58])).

fof(f726,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f725,f59])).

fof(f725,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f724,f60])).

fof(f724,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f723,f61])).

fof(f723,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f722,f62])).

fof(f722,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f721,f63])).

fof(f721,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f720,f66])).

fof(f720,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f719,f67])).

fof(f719,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f718,f68])).

fof(f718,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f82,f702])).

fof(f702,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = sK5
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f381,f686])).

fof(f686,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f685,f405])).

fof(f405,plain,(
    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f268,f381])).

fof(f268,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(resolution,[],[f151,f118])).

fof(f685,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)))
    | sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f684,f381])).

fof(f684,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f683,f418])).

fof(f683,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))
    | sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f682,f381])).

fof(f682,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f681,f406])).

fof(f406,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f109,f381])).

fof(f109,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f681,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f680,f381])).

fof(f680,plain,
    ( sK5 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f679,f381])).

fof(f679,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = sK5
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(subsumption_resolution,[],[f672,f118])).

fof(f672,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = sK5
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f214,f155])).

fof(f564,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f562,f56])).

fof(f562,plain,
    ( v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f561,f57])).

fof(f561,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f560,f58])).

fof(f560,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f559,f59])).

fof(f559,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f558,f60])).

fof(f558,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f557,f61])).

fof(f557,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f556,f122])).

fof(f556,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f555,f63])).

fof(f555,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f554,f66])).

fof(f554,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f553,f67])).

fof(f553,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f552,f68])).

fof(f552,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_7 ),
    inference(resolution,[],[f510,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f41])).

fof(f510,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f508])).

fof(f289,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f287,f59])).

fof(f287,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f286,f114])).

fof(f286,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f280,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f280,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl7_5
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f285,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f276,f282,f278])).

fof(f276,plain,
    ( sK4 = sK6
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f275,f66])).

fof(f275,plain,
    ( sK4 = sK6
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f274,f67])).

fof(f274,plain,
    ( sK4 = sK6
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f273,f68])).

fof(f273,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f272,f72])).

fof(f72,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f272,plain,
    ( sK4 = sK6
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f271,f127])).

fof(f127,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f73,f75])).

fof(f73,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f271,plain,
    ( sK4 = sK6
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f270,f217])).

fof(f217,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f74,f75])).

fof(f74,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f270,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( sK4 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f265,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f265,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    inference(forward_demodulation,[],[f76,f75])).

fof(f76,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f77,f108,f104])).

fof(f77,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f78,f108,f104])).

fof(f78,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:27:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (1138)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (1149)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.49  % (1146)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.49  % (1151)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (1130)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (1127)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (1144)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (1147)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (1145)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (1133)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (1135)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (1131)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (1128)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (1143)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (1129)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (1136)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (1132)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (1152)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (1139)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (1137)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (1141)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (1140)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (1148)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (1142)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (1134)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (1150)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.59  % (1128)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1879,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f111,f112,f285,f289,f564,f1584,f1602,f1795,f1877])).
% 0.22/0.59  fof(f1877,plain,(
% 0.22/0.59    spl7_2 | ~spl7_64),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1876])).
% 0.22/0.59  fof(f1876,plain,(
% 0.22/0.59    $false | (spl7_2 | ~spl7_64)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1861,f216])).
% 0.22/0.59  fof(f216,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)),
% 0.22/0.59    inference(subsumption_resolution,[],[f215,f69])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    v1_funct_1(sK5)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f45,f52,f51,f50,f49,f48,f47,f46])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) & sK0 = sK3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.59    inference(nnf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,negated_conjecture,(
% 0.22/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.22/0.59    inference(negated_conjecture,[],[f15])).
% 0.22/0.59  fof(f15,conjecture,(
% 0.22/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).
% 0.22/0.59  fof(f215,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | ~v1_funct_1(sK5)),
% 0.22/0.59    inference(subsumption_resolution,[],[f176,f70])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f176,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5)),
% 0.22/0.59    inference(resolution,[],[f71,f101])).
% 0.22/0.59  fof(f101,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.59  fof(f99,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.59    inference(equality_resolution,[],[f92])).
% 0.22/0.59  fof(f92,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(nnf_transformation,[],[f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f1861,plain,(
% 0.22/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) | (spl7_2 | ~spl7_64)),
% 0.22/0.59    inference(backward_demodulation,[],[f1633,f1849])).
% 0.22/0.59  fof(f1849,plain,(
% 0.22/0.59    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1848,f69])).
% 0.22/0.59  fof(f1848,plain,(
% 0.22/0.59    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1847,f70])).
% 0.22/0.59  fof(f1847,plain,(
% 0.22/0.59    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1846,f71])).
% 0.22/0.59  fof(f1846,plain,(
% 0.22/0.59    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~spl7_64),
% 0.22/0.59    inference(resolution,[],[f1844,f1659])).
% 0.22/0.59  fof(f1659,plain,(
% 0.22/0.59    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X7,k7_relat_1(sK4,u1_struct_0(sK2))) | k7_relat_1(sK4,u1_struct_0(sK2)) = X7 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X7)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f1658,f418])).
% 0.22/0.59  fof(f418,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.59    inference(subsumption_resolution,[],[f417,f113])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    l1_struct_0(sK0)),
% 0.22/0.59    inference(resolution,[],[f58,f79])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    l1_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f417,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_struct_0(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f416,f114])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    l1_struct_0(sK1)),
% 0.22/0.59    inference(resolution,[],[f61,f79])).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    l1_pre_topc(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f416,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f415,f66])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    v1_funct_1(sK4)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f415,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f414,f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f414,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f413,f68])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f413,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f409,f118])).
% 0.22/0.59  fof(f118,plain,(
% 0.22/0.59    l1_struct_0(sK2)),
% 0.22/0.59    inference(resolution,[],[f117,f79])).
% 0.22/0.59  fof(f117,plain,(
% 0.22/0.59    l1_pre_topc(sK2)),
% 0.22/0.59    inference(subsumption_resolution,[],[f116,f58])).
% 0.22/0.59  fof(f116,plain,(
% 0.22/0.59    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.59    inference(resolution,[],[f63,f80])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    m1_pre_topc(sK2,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f409,plain,(
% 0.22/0.59    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)),
% 0.22/0.59    inference(superposition,[],[f89,f381])).
% 0.22/0.59  fof(f381,plain,(
% 0.22/0.59    k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.22/0.59    inference(resolution,[],[f378,f63])).
% 0.22/0.59  fof(f378,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k7_relat_1(sK4,u1_struct_0(X6))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f163,f164])).
% 0.22/0.59  fof(f164,plain,(
% 0.22/0.59    ( ! [X7] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X7) = k7_relat_1(sK4,X7)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f133,f66])).
% 0.22/0.59  fof(f133,plain,(
% 0.22/0.59    ( ! [X7] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X7) = k7_relat_1(sK4,X7) | ~v1_funct_1(sK4)) )),
% 0.22/0.59    inference(resolution,[],[f68,f93])).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.59  fof(f163,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6))) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f162,f56])).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ~v2_struct_0(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f162,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f161,f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    v2_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f161,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f160,f58])).
% 0.22/0.59  fof(f160,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f159,f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ~v2_struct_0(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f159,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f158,f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    v2_pre_topc(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f158,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f157,f61])).
% 0.22/0.59  fof(f157,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f156,f66])).
% 0.22/0.59  fof(f156,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f132,f67])).
% 0.22/0.59  fof(f132,plain,(
% 0.22/0.59    ( ! [X6] : (~m1_pre_topc(X6,sK0) | k2_tmap_1(sK0,sK1,sK4,X6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X6)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(resolution,[],[f68,f83])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.59    inference(flattening,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.22/0.59  fof(f1658,plain,(
% 0.22/0.59    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X7,k7_relat_1(sK4,u1_struct_0(sK2))) | k7_relat_1(sK4,u1_struct_0(sK2)) = X7 | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X7)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f1642,f118])).
% 0.22/0.59  fof(f1642,plain,(
% 0.22/0.59    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X7,k7_relat_1(sK4,u1_struct_0(sK2))) | ~l1_struct_0(sK2) | k7_relat_1(sK4,u1_struct_0(sK2)) = X7 | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X7)) )),
% 0.22/0.59    inference(superposition,[],[f338,f381])).
% 0.22/0.59  fof(f338,plain,(
% 0.22/0.59    ( ! [X14,X15] : (~r2_funct_2(u1_struct_0(X14),u1_struct_0(sK1),X15,k2_tmap_1(sK0,sK1,sK4,X14)) | ~l1_struct_0(X14) | k2_tmap_1(sK0,sK1,sK4,X14) = X15 | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X14),u1_struct_0(X14),u1_struct_0(sK1)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1)))) | ~v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1)) | ~v1_funct_1(X15)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f315,f151])).
% 0.22/0.59  fof(f151,plain,(
% 0.22/0.59    ( ! [X4] : (~l1_struct_0(X4) | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4))) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f150,f113])).
% 0.22/0.59  fof(f150,plain,(
% 0.22/0.59    ( ! [X4] : (~l1_struct_0(X4) | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4)) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f149,f114])).
% 0.22/0.59  fof(f149,plain,(
% 0.22/0.59    ( ! [X4] : (~l1_struct_0(X4) | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f148,f66])).
% 0.22/0.59  fof(f148,plain,(
% 0.22/0.59    ( ! [X4] : (~l1_struct_0(X4) | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f130,f67])).
% 0.22/0.59  fof(f130,plain,(
% 0.22/0.59    ( ! [X4] : (~l1_struct_0(X4) | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(resolution,[],[f68,f88])).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f35])).
% 0.22/0.59  fof(f315,plain,(
% 0.22/0.59    ( ! [X14,X15] : (~l1_struct_0(X14) | ~r2_funct_2(u1_struct_0(X14),u1_struct_0(sK1),X15,k2_tmap_1(sK0,sK1,sK4,X14)) | k2_tmap_1(sK0,sK1,sK4,X14) = X15 | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X14),u1_struct_0(X14),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X14)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1)))) | ~v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1)) | ~v1_funct_1(X15)) )),
% 0.22/0.59    inference(resolution,[],[f155,f91])).
% 0.22/0.59  fof(f91,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f54])).
% 0.22/0.59  fof(f155,plain,(
% 0.22/0.59    ( ! [X5] : (m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~l1_struct_0(X5)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f154,f113])).
% 0.22/0.59  fof(f154,plain,(
% 0.22/0.59    ( ! [X5] : (~l1_struct_0(X5) | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f153,f114])).
% 0.22/0.59  fof(f153,plain,(
% 0.22/0.59    ( ! [X5] : (~l1_struct_0(X5) | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f152,f66])).
% 0.22/0.59  fof(f152,plain,(
% 0.22/0.59    ( ! [X5] : (~l1_struct_0(X5) | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f131,f67])).
% 0.22/0.59  fof(f131,plain,(
% 0.22/0.59    ( ! [X5] : (~l1_struct_0(X5) | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.22/0.59    inference(resolution,[],[f68,f90])).
% 0.22/0.59  fof(f90,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f35])).
% 0.22/0.59  fof(f1844,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1843,f168])).
% 0.22/0.59  fof(f168,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)),
% 0.22/0.59    inference(subsumption_resolution,[],[f167,f66])).
% 0.22/0.59  fof(f167,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | ~v1_funct_1(sK4)),
% 0.22/0.59    inference(subsumption_resolution,[],[f135,f67])).
% 0.22/0.59  fof(f135,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4)),
% 0.22/0.59    inference(resolution,[],[f68,f101])).
% 0.22/0.59  fof(f1843,plain,(
% 0.22/0.59    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~spl7_64),
% 0.22/0.59    inference(forward_demodulation,[],[f1842,f383])).
% 0.22/0.59  fof(f383,plain,(
% 0.22/0.59    sK4 = k2_tmap_1(sK0,sK1,sK4,sK0)),
% 0.22/0.59    inference(forward_demodulation,[],[f382,f219])).
% 0.22/0.59  fof(f219,plain,(
% 0.22/0.59    sK4 = k7_relat_1(sK4,u1_struct_0(sK0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f218,f137])).
% 0.22/0.59  fof(f137,plain,(
% 0.22/0.59    v1_relat_1(sK4)),
% 0.22/0.59    inference(resolution,[],[f68,f86])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.59  fof(f218,plain,(
% 0.22/0.59    sK4 = k7_relat_1(sK4,u1_struct_0(sK0)) | ~v1_relat_1(sK4)),
% 0.22/0.59    inference(resolution,[],[f136,f85])).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.59  fof(f136,plain,(
% 0.22/0.59    v4_relat_1(sK4,u1_struct_0(sK0))),
% 0.22/0.59    inference(resolution,[],[f68,f87])).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.59    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.59  fof(f382,plain,(
% 0.22/0.59    k7_relat_1(sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)),
% 0.22/0.59    inference(resolution,[],[f378,f122])).
% 0.22/0.59  fof(f122,plain,(
% 0.22/0.59    m1_pre_topc(sK0,sK0)),
% 0.22/0.59    inference(backward_demodulation,[],[f65,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    sK0 = sK3),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    m1_pre_topc(sK3,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f1842,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1841,f56])).
% 0.22/0.59  fof(f1841,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | v2_struct_0(sK0) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1840,f122])).
% 0.22/0.59  fof(f1840,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1839,f66])).
% 0.22/0.59  fof(f1839,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1838,f67])).
% 0.22/0.59  fof(f1838,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1837,f68])).
% 0.22/0.59  fof(f1837,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~spl7_64),
% 0.22/0.59    inference(subsumption_resolution,[],[f1826,f63])).
% 0.22/0.59  fof(f1826,plain,(
% 0.22/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~spl7_64),
% 0.22/0.59    inference(superposition,[],[f429,f1601])).
% 0.22/0.59  fof(f1601,plain,(
% 0.22/0.59    sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~spl7_64),
% 0.22/0.59    inference(avatar_component_clause,[],[f1599])).
% 0.22/0.59  fof(f1599,plain,(
% 0.22/0.59    spl7_64 <=> sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.22/0.59  fof(f429,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f428,f56])).
% 0.22/0.59  fof(f428,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f427,f57])).
% 0.22/0.59  fof(f427,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f426,f58])).
% 0.22/0.59  fof(f426,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f425,f59])).
% 0.22/0.59  fof(f425,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f424,f60])).
% 0.22/0.59  fof(f424,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f423,f61])).
% 0.22/0.59  fof(f423,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f422,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ~v2_struct_0(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f422,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f421,f63])).
% 0.22/0.59  fof(f421,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f420,f66])).
% 0.22/0.59  fof(f420,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f419,f67])).
% 0.22/0.59  fof(f419,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f410,f68])).
% 1.82/0.61  fof(f410,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),k7_relat_1(sK4,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(superposition,[],[f82,f381])).
% 1.82/0.61  fof(f82,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f25])).
% 1.82/0.61  fof(f25,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.61    inference(flattening,[],[f24])).
% 1.82/0.61  fof(f24,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.61    inference(ennf_transformation,[],[f13])).
% 1.82/0.61  fof(f13,axiom,(
% 1.82/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).
% 1.82/0.61  fof(f1633,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | spl7_2),
% 1.82/0.61    inference(backward_demodulation,[],[f110,f381])).
% 1.82/0.61  fof(f110,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | spl7_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f108])).
% 1.82/0.61  fof(f108,plain,(
% 1.82/0.61    spl7_2 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.82/0.61  fof(f1795,plain,(
% 1.82/0.61    ~spl7_1 | ~spl7_6 | spl7_63),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1794])).
% 1.82/0.61  fof(f1794,plain,(
% 1.82/0.61    $false | (~spl7_1 | ~spl7_6 | spl7_63)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1597,f1629])).
% 1.82/0.61  fof(f1629,plain,(
% 1.82/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | (~spl7_1 | ~spl7_6)),
% 1.82/0.61    inference(forward_demodulation,[],[f1628,f75])).
% 1.82/0.61  fof(f1628,plain,(
% 1.82/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl7_1 | ~spl7_6)),
% 1.82/0.61    inference(forward_demodulation,[],[f105,f284])).
% 1.82/0.61  fof(f284,plain,(
% 1.82/0.61    sK4 = sK6 | ~spl7_6),
% 1.82/0.61    inference(avatar_component_clause,[],[f282])).
% 1.82/0.61  fof(f282,plain,(
% 1.82/0.61    spl7_6 <=> sK4 = sK6),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.82/0.61  fof(f105,plain,(
% 1.82/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) | ~spl7_1),
% 1.82/0.61    inference(avatar_component_clause,[],[f104])).
% 1.82/0.61  fof(f104,plain,(
% 1.82/0.61    spl7_1 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.82/0.61  fof(f1597,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | spl7_63),
% 1.82/0.61    inference(avatar_component_clause,[],[f1595])).
% 1.82/0.61  fof(f1595,plain,(
% 1.82/0.61    spl7_63 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 1.82/0.61  fof(f1602,plain,(
% 1.82/0.61    ~spl7_63 | spl7_64 | ~spl7_7),
% 1.82/0.61    inference(avatar_split_clause,[],[f1593,f508,f1599,f1595])).
% 1.82/0.61  fof(f508,plain,(
% 1.82/0.61    spl7_7 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.82/0.61  fof(f1593,plain,(
% 1.82/0.61    sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f1592,f478])).
% 1.82/0.61  fof(f478,plain,(
% 1.82/0.61    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.82/0.61    inference(resolution,[],[f473,f63])).
% 1.82/0.61  fof(f473,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f472,f56])).
% 1.82/0.61  fof(f472,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f471,f57])).
% 1.82/0.61  fof(f471,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f470,f58])).
% 1.82/0.61  fof(f470,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(resolution,[],[f142,f122])).
% 1.82/0.61  fof(f142,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f141,f59])).
% 1.82/0.61  fof(f141,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f140,f60])).
% 1.82/0.61  fof(f140,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f139,f61])).
% 1.82/0.61  fof(f139,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f138,f66])).
% 1.82/0.61  fof(f138,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f128,f67])).
% 1.82/0.61  fof(f128,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(resolution,[],[f68,f94])).
% 1.82/0.61  fof(f94,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f41])).
% 1.82/0.61  fof(f41,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.61    inference(flattening,[],[f40])).
% 1.82/0.61  fof(f40,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.61    inference(ennf_transformation,[],[f12])).
% 1.82/0.61  fof(f12,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.82/0.61  fof(f1592,plain,(
% 1.82/0.61    sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f674,f509])).
% 1.82/0.61  fof(f509,plain,(
% 1.82/0.61    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl7_7),
% 1.82/0.61    inference(avatar_component_clause,[],[f508])).
% 1.82/0.61  fof(f674,plain,(
% 1.82/0.61    sK5 = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.82/0.61    inference(resolution,[],[f214,f487])).
% 1.82/0.61  fof(f487,plain,(
% 1.82/0.61    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.82/0.61    inference(resolution,[],[f486,f63])).
% 1.82/0.61  fof(f486,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f485,f56])).
% 1.82/0.61  fof(f485,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f484,f57])).
% 1.82/0.61  fof(f484,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f483,f58])).
% 1.82/0.61  fof(f483,plain,(
% 1.82/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.82/0.61    inference(resolution,[],[f147,f122])).
% 1.82/0.61  fof(f147,plain,(
% 1.82/0.61    ( ! [X2,X3] : (~m1_pre_topc(sK0,X2) | ~m1_pre_topc(X3,X2) | m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f146,f59])).
% 1.82/0.61  fof(f146,plain,(
% 1.82/0.61    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK0,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f145,f60])).
% 1.82/0.61  fof(f145,plain,(
% 1.82/0.61    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK0,X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f144,f61])).
% 1.82/0.61  fof(f144,plain,(
% 1.82/0.61    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK0,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f143,f66])).
% 1.82/0.61  fof(f143,plain,(
% 1.82/0.61    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK0,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f129,f67])).
% 1.82/0.61  fof(f129,plain,(
% 1.82/0.61    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK0,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK0,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.82/0.61    inference(resolution,[],[f68,f96])).
% 1.82/0.61  fof(f96,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f41])).
% 1.82/0.61  fof(f214,plain,(
% 1.82/0.61    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | sK5 = X8 | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X8,sK5) | ~v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X8)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f213,f69])).
% 1.82/0.61  fof(f213,plain,(
% 1.82/0.61    ( ! [X8] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X8,sK5) | sK5 = X8 | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X8)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f175,f70])).
% 1.82/0.61  fof(f175,plain,(
% 1.82/0.61    ( ! [X8] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X8,sK5) | sK5 = X8 | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X8)) )),
% 1.82/0.61    inference(resolution,[],[f71,f91])).
% 1.82/0.61  fof(f1584,plain,(
% 1.82/0.61    spl7_1 | ~spl7_2 | ~spl7_6),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f1583])).
% 1.82/0.61  fof(f1583,plain,(
% 1.82/0.61    $false | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1582,f168])).
% 1.82/0.61  fof(f1582,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(forward_demodulation,[],[f1581,f383])).
% 1.82/0.61  fof(f1581,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1580,f56])).
% 1.82/0.61  fof(f1580,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | v2_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1579,f122])).
% 1.82/0.61  fof(f1579,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1578,f66])).
% 1.82/0.61  fof(f1578,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1577,f67])).
% 1.82/0.61  fof(f1577,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1576,f68])).
% 1.82/0.61  fof(f1576,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(subsumption_resolution,[],[f1574,f63])).
% 1.82/0.61  fof(f1574,plain,(
% 1.82/0.61    ~m1_pre_topc(sK2,sK0) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_6)),
% 1.82/0.61    inference(resolution,[],[f729,f304])).
% 1.82/0.61  fof(f304,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | (spl7_1 | ~spl7_6)),
% 1.82/0.61    inference(forward_demodulation,[],[f303,f75])).
% 1.82/0.61  fof(f303,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (spl7_1 | ~spl7_6)),
% 1.82/0.61    inference(forward_demodulation,[],[f106,f284])).
% 1.82/0.61  fof(f106,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) | spl7_1),
% 1.82/0.61    inference(avatar_component_clause,[],[f104])).
% 1.82/0.61  fof(f729,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f728,f56])).
% 1.82/0.61  fof(f728,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f727,f57])).
% 1.82/0.61  fof(f727,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f726,f58])).
% 1.82/0.61  fof(f726,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f725,f59])).
% 1.82/0.61  fof(f725,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f724,f60])).
% 1.82/0.61  fof(f724,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f723,f61])).
% 1.82/0.61  fof(f723,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f722,f62])).
% 1.82/0.61  fof(f722,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f721,f63])).
% 1.82/0.61  fof(f721,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f720,f66])).
% 1.82/0.61  fof(f720,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f719,f67])).
% 1.82/0.61  fof(f719,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f718,f68])).
% 1.82/0.61  fof(f718,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0,sK2,X1),sK5) | ~m1_pre_topc(sK2,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK0,sK1,sK4,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.82/0.61    inference(superposition,[],[f82,f702])).
% 1.82/0.61  fof(f702,plain,(
% 1.82/0.61    k2_tmap_1(sK0,sK1,sK4,sK2) = sK5 | ~spl7_2),
% 1.82/0.61    inference(backward_demodulation,[],[f381,f686])).
% 1.82/0.61  fof(f686,plain,(
% 1.82/0.61    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f685,f405])).
% 1.82/0.61  fof(f405,plain,(
% 1.82/0.61    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)))),
% 1.82/0.61    inference(backward_demodulation,[],[f268,f381])).
% 1.82/0.61  fof(f268,plain,(
% 1.82/0.61    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.82/0.61    inference(resolution,[],[f151,f118])).
% 1.82/0.61  fof(f685,plain,(
% 1.82/0.61    ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2))) | sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~spl7_2),
% 1.82/0.61    inference(forward_demodulation,[],[f684,f381])).
% 1.82/0.61  fof(f684,plain,(
% 1.82/0.61    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f683,f418])).
% 1.82/0.61  fof(f683,plain,(
% 1.82/0.61    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) | sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~spl7_2),
% 1.82/0.61    inference(forward_demodulation,[],[f682,f381])).
% 1.82/0.61  fof(f682,plain,(
% 1.82/0.61    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~spl7_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f681,f406])).
% 1.82/0.61  fof(f406,plain,(
% 1.82/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | ~spl7_2),
% 1.82/0.61    inference(backward_demodulation,[],[f109,f381])).
% 1.82/0.61  fof(f109,plain,(
% 1.82/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~spl7_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f108])).
% 1.82/0.61  fof(f681,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.82/0.61    inference(forward_demodulation,[],[f680,f381])).
% 1.82/0.61  fof(f680,plain,(
% 1.82/0.61    sK5 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.82/0.61    inference(forward_demodulation,[],[f679,f381])).
% 1.82/0.61  fof(f679,plain,(
% 1.82/0.61    k2_tmap_1(sK0,sK1,sK4,sK2) = sK5 | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.82/0.61    inference(subsumption_resolution,[],[f672,f118])).
% 1.82/0.61  fof(f672,plain,(
% 1.82/0.61    k2_tmap_1(sK0,sK1,sK4,sK2) = sK5 | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_struct_0(sK2)),
% 1.82/0.61    inference(resolution,[],[f214,f155])).
% 1.82/0.61  fof(f564,plain,(
% 1.82/0.61    spl7_7),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f563])).
% 1.82/0.61  fof(f563,plain,(
% 1.82/0.61    $false | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f562,f56])).
% 1.82/0.61  fof(f562,plain,(
% 1.82/0.61    v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f561,f57])).
% 1.82/0.61  fof(f561,plain,(
% 1.82/0.61    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f560,f58])).
% 1.82/0.61  fof(f560,plain,(
% 1.82/0.61    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f559,f59])).
% 1.82/0.61  fof(f559,plain,(
% 1.82/0.61    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f558,f60])).
% 1.82/0.61  fof(f558,plain,(
% 1.82/0.61    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f557,f61])).
% 1.82/0.61  fof(f557,plain,(
% 1.82/0.61    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f556,f122])).
% 1.82/0.61  fof(f556,plain,(
% 1.82/0.61    ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f555,f63])).
% 1.82/0.61  fof(f555,plain,(
% 1.82/0.61    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f554,f66])).
% 1.82/0.61  fof(f554,plain,(
% 1.82/0.61    ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f553,f67])).
% 1.82/0.61  fof(f553,plain,(
% 1.82/0.61    ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(subsumption_resolution,[],[f552,f68])).
% 1.82/0.61  fof(f552,plain,(
% 1.82/0.61    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl7_7),
% 1.82/0.61    inference(resolution,[],[f510,f95])).
% 1.82/0.61  fof(f95,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f41])).
% 1.82/0.61  fof(f510,plain,(
% 1.82/0.61    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | spl7_7),
% 1.82/0.61    inference(avatar_component_clause,[],[f508])).
% 1.82/0.61  fof(f289,plain,(
% 1.82/0.61    ~spl7_5),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f288])).
% 1.82/0.61  fof(f288,plain,(
% 1.82/0.61    $false | ~spl7_5),
% 1.82/0.61    inference(subsumption_resolution,[],[f287,f59])).
% 1.82/0.61  fof(f287,plain,(
% 1.82/0.61    v2_struct_0(sK1) | ~spl7_5),
% 1.82/0.61    inference(subsumption_resolution,[],[f286,f114])).
% 1.82/0.61  fof(f286,plain,(
% 1.82/0.61    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl7_5),
% 1.82/0.61    inference(resolution,[],[f280,f81])).
% 1.82/0.61  fof(f81,plain,(
% 1.82/0.61    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f23])).
% 1.82/0.61  fof(f23,plain,(
% 1.82/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.82/0.61    inference(flattening,[],[f22])).
% 1.82/0.61  fof(f22,plain,(
% 1.82/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.82/0.61    inference(ennf_transformation,[],[f8])).
% 1.82/0.61  fof(f8,axiom,(
% 1.82/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.82/0.61  fof(f280,plain,(
% 1.82/0.61    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_5),
% 1.82/0.61    inference(avatar_component_clause,[],[f278])).
% 1.82/0.61  fof(f278,plain,(
% 1.82/0.61    spl7_5 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.82/0.61  fof(f285,plain,(
% 1.82/0.61    spl7_5 | spl7_6),
% 1.82/0.61    inference(avatar_split_clause,[],[f276,f282,f278])).
% 1.82/0.61  fof(f276,plain,(
% 1.82/0.61    sK4 = sK6 | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(subsumption_resolution,[],[f275,f66])).
% 1.82/0.61  fof(f275,plain,(
% 1.82/0.61    sK4 = sK6 | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(subsumption_resolution,[],[f274,f67])).
% 1.82/0.61  fof(f274,plain,(
% 1.82/0.61    sK4 = sK6 | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(subsumption_resolution,[],[f273,f68])).
% 1.82/0.61  fof(f273,plain,(
% 1.82/0.61    sK4 = sK6 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(subsumption_resolution,[],[f272,f72])).
% 1.82/0.61  fof(f72,plain,(
% 1.82/0.61    v1_funct_1(sK6)),
% 1.82/0.61    inference(cnf_transformation,[],[f53])).
% 1.82/0.61  fof(f272,plain,(
% 1.82/0.61    sK4 = sK6 | ~v1_funct_1(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(subsumption_resolution,[],[f271,f127])).
% 1.82/0.61  fof(f127,plain,(
% 1.82/0.61    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.82/0.61    inference(forward_demodulation,[],[f73,f75])).
% 1.82/0.61  fof(f73,plain,(
% 1.82/0.61    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.82/0.61    inference(cnf_transformation,[],[f53])).
% 1.82/0.61  fof(f271,plain,(
% 1.82/0.61    sK4 = sK6 | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(subsumption_resolution,[],[f270,f217])).
% 1.82/0.61  fof(f217,plain,(
% 1.82/0.61    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.82/0.61    inference(forward_demodulation,[],[f74,f75])).
% 1.82/0.61  fof(f74,plain,(
% 1.82/0.61    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.82/0.61    inference(cnf_transformation,[],[f53])).
% 1.82/0.61  fof(f270,plain,(
% 1.82/0.61    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(duplicate_literal_removal,[],[f269])).
% 1.82/0.61  fof(f269,plain,(
% 1.82/0.61    sK4 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 1.82/0.61    inference(resolution,[],[f265,f97])).
% 1.82/0.61  fof(f97,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f55])).
% 1.82/0.61  fof(f55,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.82/0.61    inference(nnf_transformation,[],[f43])).
% 1.82/0.61  fof(f43,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.82/0.61    inference(flattening,[],[f42])).
% 1.82/0.61  fof(f42,plain,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.82/0.61    inference(ennf_transformation,[],[f9])).
% 1.82/0.61  fof(f9,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.82/0.61  fof(f265,plain,(
% 1.82/0.61    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 1.82/0.61    inference(forward_demodulation,[],[f76,f75])).
% 1.82/0.61  fof(f76,plain,(
% 1.82/0.61    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 1.82/0.61    inference(cnf_transformation,[],[f53])).
% 1.82/0.61  fof(f112,plain,(
% 1.82/0.61    spl7_1 | spl7_2),
% 1.82/0.61    inference(avatar_split_clause,[],[f77,f108,f104])).
% 1.82/0.61  fof(f77,plain,(
% 1.82/0.61    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.82/0.61    inference(cnf_transformation,[],[f53])).
% 1.82/0.61  fof(f111,plain,(
% 1.82/0.61    ~spl7_1 | ~spl7_2),
% 1.82/0.61    inference(avatar_split_clause,[],[f78,f108,f104])).
% 1.82/0.61  fof(f78,plain,(
% 1.82/0.61    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.82/0.61    inference(cnf_transformation,[],[f53])).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (1128)------------------------------
% 1.82/0.61  % (1128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (1128)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (1128)Memory used [KB]: 11769
% 1.82/0.61  % (1128)Time elapsed: 0.162 s
% 1.82/0.61  % (1128)------------------------------
% 1.82/0.61  % (1128)------------------------------
% 1.82/0.61  % (1126)Success in time 0.243 s
%------------------------------------------------------------------------------

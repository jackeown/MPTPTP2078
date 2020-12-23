%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 989 expanded)
%              Number of leaves         :   15 ( 492 expanded)
%              Depth                    :   57
%              Number of atoms          :  983 (19326 expanded)
%              Number of equality atoms :  140 (1281 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f182,f90])).

fof(f90,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    inference(subsumption_resolution,[],[f89,f48])).

fof(f48,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & ! [X6] :
        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
        | ~ r2_hidden(X6,u1_struct_0(sK2))
        | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f28,f27,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & ! [X6] :
                                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                                | ~ r2_hidden(X6,u1_struct_0(X2))
                                | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X2,X3)
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
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                        & ! [X6] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                            | ~ r2_hidden(X6,u1_struct_0(X2))
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                      & ! [X6] :
                          ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                          | ~ r2_hidden(X6,u1_struct_0(X2))
                          | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                    & ! [X6] :
                        ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                        | ~ r2_hidden(X6,u1_struct_0(X2))
                        | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                  & ! [X6] :
                      ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                      | ~ r2_hidden(X6,u1_struct_0(sK2))
                      | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                & ! [X6] :
                    ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                    | ~ r2_hidden(X6,u1_struct_0(sK2))
                    | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
              & ! [X6] :
                  ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                  | ~ r2_hidden(X6,u1_struct_0(sK2))
                  | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
            & ! [X6] :
                ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6)
                | ~ r2_hidden(X6,u1_struct_0(sK2))
                | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
          & ! [X6] :
              ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
              | ~ r2_hidden(X6,u1_struct_0(sK2))
              | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X5] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
        & ! [X6] :
            ( k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6)
            | ~ r2_hidden(X6,u1_struct_0(sK2))
            | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
      & ! [X6] :
          ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
          | ~ r2_hidden(X6,u1_struct_0(sK2))
          | ~ m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & ! [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6)
                              | ~ r2_hidden(X6,u1_struct_0(X2))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X3))
                                   => ( r2_hidden(X6,u1_struct_0(X2))
                                     => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).

fof(f89,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK5,X2,X3)
      | r2_funct_2(X2,X3,sK5,sK5) ) ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f182,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5) ),
    inference(superposition,[],[f51,f181])).

fof(f181,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f180,f38])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f180,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f179,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f179,plain,
    ( ~ l1_struct_0(sK1)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f178,f66])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f178,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f177,f55])).

fof(f177,plain,
    ( ~ l1_struct_0(sK2)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f176,f67])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f176,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f175,f55])).

fof(f175,plain,
    ( ~ l1_struct_0(sK3)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f174,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f173,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f173,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f172,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f172,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f171,f58])).

fof(f171,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f170,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f170,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f169,f58])).

fof(f169,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f168,f67])).

fof(f168,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f167,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f166,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f166,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(forward_demodulation,[],[f164,f130])).

fof(f130,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f129,f44])).

fof(f44,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f129,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f128,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,
    ( ~ v1_funct_1(sK4)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f127,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(X1)
      | k3_tmap_1(sK0,sK1,sK3,sK2,X1) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f126,f42])).

fof(f126,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,sK0)
      | k3_tmap_1(sK0,sK1,sK3,sK2,X1) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f123,f46])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(sK0,sK1,X1,sK2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(sK2))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f106,f40])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,sK0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X1) ) ),
    inference(subsumption_resolution,[],[f105,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v2_pre_topc(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4))
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f85,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | ~ l1_pre_topc(sK1)
      | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f164,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f163,f43])).

fof(f163,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f162,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f161,f45])).

fof(f161,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f160,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f159,f48])).

fof(f159,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f158,f49])).

fof(f158,plain,
    ( sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(superposition,[],[f54,f156])).

fof(f156,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f155,f38])).

fof(f155,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f154,f55])).

fof(f154,plain,
    ( ~ l1_struct_0(sK1)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 ),
    inference(subsumption_resolution,[],[f153,f66])).

fof(f153,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f152,f55])).

% (18186)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (18181)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (18173)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (18172)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f152,plain,
    ( ~ l1_struct_0(sK2)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f151,f67])).

fof(f151,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f150,f55])).

fof(f150,plain,
    ( ~ l1_struct_0(sK3)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f149,f36])).

fof(f149,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f148,f58])).

fof(f148,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f147,f39])).

fof(f147,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f146,f58])).

fof(f146,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f145,f41])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f144,f58])).

fof(f144,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) ),
    inference(forward_demodulation,[],[f143,f130])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f142,f43])).

fof(f142,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f141,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))
    | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f140,f45])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f139,f67])).

fof(f139,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ l1_pre_topc(sK3)
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f138,f46])).

fof(f138,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(sK3)
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(sK3)
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2))
      | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f136,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(X0))
      | sK5 = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f114,f57])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
      | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | m1_subset_1(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f113,f48])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),X0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | m1_subset_1(sK6(X4,X5,X6,X7,sK5),X4)
      | ~ v1_funct_2(sK5,X7,X5)
      | sK5 = k2_partfun1(X4,X5,X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X4))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X5)
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f52,f47])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
                        & r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f30])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5))
      | sK5 = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f134,f50])).

fof(f50,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | sK5 = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f121,f57])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
      | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | r2_hidden(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK2))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,X0,u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f80,f49])).

fof(f80,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | r2_hidden(sK6(X4,X5,X6,X7,sK5),X7)
      | ~ v1_funct_2(sK5,X7,X5)
      | sK5 = k2_partfun1(X4,X5,X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X4))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(X5)
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f53,f47])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | r2_hidden(sK6(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (18177)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (18177)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f182,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)),
% 0.20/0.52    inference(subsumption_resolution,[],[f89,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    (((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & ! [X6] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f28,f27,f26,f25,f24,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ? [X5] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & ! [X6] : (k1_funct_1(X5,X6) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & ! [X6] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) | ~r2_hidden(X6,u1_struct_0(sK2)) | ~m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & ! [X6] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) | ~r2_hidden(X6,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)),
% 0.20/0.52    inference(resolution,[],[f71,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK5,X2,X3) | r2_funct_2(X2,X3,sK5,sK5)) )),
% 0.20/0.52    inference(resolution,[],[f63,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    v1_funct_1(sK5)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.52    inference(equality_resolution,[],[f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK5)),
% 0.20/0.52    inference(superposition,[],[f51,f181])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    l1_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f179,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ~l1_struct_0(sK1) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f178,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    l1_pre_topc(sK2)),
% 0.20/0.52    inference(resolution,[],[f64,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.20/0.52    inference(resolution,[],[f56,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK1) | ~l1_pre_topc(sK2)),
% 0.20/0.52    inference(resolution,[],[f177,f55])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ~l1_struct_0(sK2) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f176,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    l1_pre_topc(sK3)),
% 0.20/0.52    inference(resolution,[],[f64,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK2) | ~l1_struct_0(sK1) | ~l1_pre_topc(sK3)),
% 0.20/0.52    inference(resolution,[],[f175,f55])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    ~l1_struct_0(sK3) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK2) | ~l1_struct_0(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f174,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.20/0.52    inference(resolution,[],[f173,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f172,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ~v2_struct_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f171,f58])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f170,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ~v2_struct_0(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.52    inference(resolution,[],[f169,f58])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f168,f67])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~l1_pre_topc(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f167,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3)),
% 0.20/0.52    inference(resolution,[],[f166,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(forward_demodulation,[],[f164,f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f129,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f128,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ~v1_funct_1(sK4) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.52    inference(resolution,[],[f127,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X1) | k3_tmap_1(sK0,sK1,sK3,sK2,X1) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X1,u1_struct_0(sK2)) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f126,f42])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,X1) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X1,u1_struct_0(sK2)) | ~v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 0.20/0.52    inference(resolution,[],[f123,f46])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,sK2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(sK2)) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))) )),
% 0.20/0.52    inference(resolution,[],[f106,f40])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2)) | ~m1_pre_topc(X2,X1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f105,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2)) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f103,f35])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2)) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f86,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (~v2_pre_topc(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~v1_funct_1(X6) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4)) | ~l1_pre_topc(X7) | ~m1_pre_topc(X4,X5) | v2_struct_0(X7)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f85,f36])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~v1_funct_1(X6) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4)) | v2_struct_0(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f82,f38])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~v1_funct_1(X6) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | ~l1_pre_topc(sK1) | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4)) | v2_struct_0(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 0.20/0.52    inference(resolution,[],[f59,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    v2_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f163,f43])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f162,f44])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f161,f45])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f160,f47])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f159,f48])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f158,f49])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f157])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) != k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(superposition,[],[f54,f156])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f155,f38])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_pre_topc(sK1)),
% 0.20/0.52    inference(resolution,[],[f154,f55])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    ~l1_struct_0(sK1) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5),
% 0.20/0.52    inference(subsumption_resolution,[],[f153,f66])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK1) | ~l1_pre_topc(sK2)),
% 0.20/0.52    inference(resolution,[],[f152,f55])).
% 0.20/0.52  % (18186)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (18181)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (18173)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (18172)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ~l1_struct_0(sK2) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f151,f67])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK2) | ~l1_struct_0(sK1) | ~l1_pre_topc(sK3)),
% 0.20/0.54    inference(resolution,[],[f150,f55])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ~l1_struct_0(sK3) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | ~l1_struct_0(sK2) | ~l1_struct_0(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f149,f36])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.20/0.54    inference(resolution,[],[f148,f58])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f147,f39])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.20/0.54    inference(resolution,[],[f146,f58])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK3)),
% 0.20/0.54    inference(subsumption_resolution,[],[f145,f41])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.54    inference(resolution,[],[f144,f58])).
% 0.20/0.54  fof(f144,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = sK5 | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5))),
% 0.20/0.54    inference(forward_demodulation,[],[f143,f130])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f142,f43])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.54    inference(subsumption_resolution,[],[f141,f44])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.20/0.54    inference(resolution,[],[f140,f45])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f139,f67])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f138,f46])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2)) | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X0,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3)) )),
% 0.20/0.54    inference(resolution,[],[f136,f132])).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(X0)) | sK5 = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(resolution,[],[f114,f57])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0)) | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2)) | m1_subset_1(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),X0) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(X1,X0,u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f113,f48])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),X0) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(X1,X0,u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f76,f49])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | m1_subset_1(sK6(X4,X5,X6,X7,sK5),X4) | ~v1_funct_2(sK5,X7,X5) | sK5 = k2_partfun1(X4,X5,X6,X7) | ~m1_subset_1(X7,k1_zfmisc_1(X4)) | v1_xboole_0(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | v1_xboole_0(X5) | v1_xboole_0(X4)) )),
% 0.20/0.54    inference(resolution,[],[f52,f47])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | k2_partfun1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | (k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) => (k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : ((k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3)) & m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X4,X3,X1) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,X0) => (r2_hidden(X5,X3) => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5))) => k2_partfun1(X0,X1,X2,X3) = X4))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5)) = k1_funct_1(sK5,sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5)) | sK5 = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2))) )),
% 0.20/0.54    inference(resolution,[],[f134,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X6] : (~r2_hidden(X6,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X6) = k1_funct_1(sK5,X6) | ~m1_subset_1(X6,u1_struct_0(sK3))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK6(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | sK5 = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),X1,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(resolution,[],[f121,f57])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0)) | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2)) | r2_hidden(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(X1,X0,u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f120,f48])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2),sK5),u1_struct_0(sK2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | sK5 = k2_partfun1(X0,u1_struct_0(sK1),X1,u1_struct_0(sK2)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_funct_2(X1,X0,u1_struct_0(sK1)) | ~v1_funct_1(X1) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f80,f49])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | r2_hidden(sK6(X4,X5,X6,X7,sK5),X7) | ~v1_funct_2(sK5,X7,X5) | sK5 = k2_partfun1(X4,X5,X6,X7) | ~m1_subset_1(X7,k1_zfmisc_1(X4)) | v1_xboole_0(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | v1_xboole_0(X5) | v1_xboole_0(X4)) )),
% 0.20/0.54    inference(resolution,[],[f53,f47])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | r2_hidden(sK6(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | k2_partfun1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) | k2_partfun1(X0,X1,X2,X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (18177)------------------------------
% 0.20/0.54  % (18177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18177)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (18177)Memory used [KB]: 1918
% 0.20/0.54  % (18177)Time elapsed: 0.115 s
% 0.20/0.54  % (18177)------------------------------
% 0.20/0.54  % (18177)------------------------------
% 0.20/0.54  % (18160)Success in time 0.184 s
%------------------------------------------------------------------------------

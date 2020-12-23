%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:34 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 681 expanded)
%              Number of leaves         :   15 ( 339 expanded)
%              Depth                    :   62
%              Number of atoms          : 1065 (17171 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f145])).

fof(f145,plain,(
    ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(resolution,[],[f144,f51])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
    & m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
    & v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK4,sK1,sK2)
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                              | ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                              | ~ v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                              | ~ v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                            & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X4,X1,X2)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                          ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                            | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                            | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                          & m1_subset_1(k2_tmap_1(sK0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK0,X1,X5,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK0,X1,X5,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X4,X1,X2)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                          | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                          | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                        & m1_subset_1(k2_tmap_1(sK0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK0,X1,X5,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK0,X1,X5,X3))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v5_pre_topc(X4,X1,X2)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                        | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                        | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                        | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3)) )
                      & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                      & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                  & v5_pre_topc(X4,sK1,X2)
                  & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                      | ~ v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                      | ~ v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                      | ~ v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3)) )
                    & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                    & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                & v5_pre_topc(X4,sK1,X2)
                & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),X3,sK2)
                    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(sK2))
                    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3)) )
                  & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                  & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
              & v5_pre_topc(X4,sK1,sK2)
              & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                  | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),X3,sK2)
                  | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(sK2))
                  | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3)) )
                & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1)
                & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
            & v5_pre_topc(X4,sK1,sK2)
            & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),sK3,sK2)
                | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
                | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3)) )
              & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
              & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v5_pre_topc(X4,sK1,sK2)
          & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),sK3,sK2)
              | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
              | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3)) )
            & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
            & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v5_pre_topc(X4,sK1,sK2)
        & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),sK3,sK2)
            | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
            | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3)) )
          & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
          & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v5_pre_topc(sK4,sK1,sK2)
      & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),sK3,sK2)
          | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
          | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3)) )
        & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1)
        & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
      & m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
      & v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                            | ~ v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                            | ~ v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                          & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X4,X1,X2)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            | ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                            | ~ v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                            | ~ v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) )
                          & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X4,X1,X2)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v5_pre_topc(X4,X1,X2)
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                                & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)) )
                             => ( m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                                & v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                                & v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                                & v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X4,X1,X2)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)) )
                           => ( m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                              & v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                              & v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2))
                              & v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tmap_1)).

fof(f144,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f49,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f140,f45])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f140,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f138,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f67,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f138,plain,(
    ~ v1_funct_1(k5_relat_1(sK5,sK4)) ),
    inference(subsumption_resolution,[],[f137,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f137,plain,
    ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f136,f44])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f135,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f133,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f132,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f131,f50])).

fof(f50,plain,(
    v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f129,f48])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f128,f51])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_1(sK5) ) ),
    inference(condensation,[],[f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3)))
      | ~ v1_funct_1(sK5) ) ),
    inference(condensation,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK2))))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3)))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f123,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f68,f66])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f122,f49])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
      | ~ v1_funct_2(sK4,X1,u1_struct_0(sK2))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),X1)
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
      | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
      | ~ v1_funct_1(k5_relat_1(sK5,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f119,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f119,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4)) ),
    inference(subsumption_resolution,[],[f118,f36])).

fof(f118,plain,
    ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f117,f57])).

fof(f117,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,
    ( ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f115,f57])).

fof(f115,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f114,f57])).

fof(f114,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f113,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f112,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f107,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f77,f106])).

fof(f106,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f105,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f103,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f99,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5) ),
    inference(superposition,[],[f96,f66])).

fof(f96,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f41,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f93,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f92,f45])).

fof(f92,plain,
    ( ~ v1_funct_1(sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f91,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f90,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f89,f47])).

fof(f47,plain,(
    v5_pre_topc(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f85,f49])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f84,f50])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f83,f51])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK1,X1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f82,f54])).

fof(f54,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
      | ~ v5_pre_topc(X2,X0,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
      | ~ v5_pre_topc(X2,X0,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f35])).

% (32465)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (32480)Refutation not found, incomplete strategy% (32480)------------------------------
% (32480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32480)Termination reason: Refutation not found, incomplete strategy

% (32480)Memory used [KB]: 1791
% (32480)Time elapsed: 0.109 s
% (32480)------------------------------
% (32480)------------------------------
fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
      | ~ v5_pre_topc(X2,X0,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
      | ~ v5_pre_topc(X2,X0,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
      | ~ v5_pre_topc(X2,X0,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f60,f44])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
      | ~ v5_pre_topc(X4,X1,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          | ~ v5_pre_topc(X4,X1,X2)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          | ~ v5_pre_topc(X4,X1,X2)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                              & v5_pre_topc(X4,X1,X2) )
                           => v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tmap_1)).

fof(f77,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f76,f49])).

fof(f76,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f75,f51])).

fof(f75,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f74,f45])).

fof(f74,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f73,f48])).

fof(f73,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5) ),
    inference(superposition,[],[f56,f66])).

fof(f56,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:49:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (824049664)
% 0.15/0.37  ipcrm: permission denied for id (824082433)
% 0.15/0.37  ipcrm: permission denied for id (824115203)
% 0.15/0.39  ipcrm: permission denied for id (824410126)
% 0.15/0.39  ipcrm: permission denied for id (824442895)
% 0.15/0.40  ipcrm: permission denied for id (824508437)
% 0.22/0.40  ipcrm: permission denied for id (824606744)
% 0.22/0.40  ipcrm: permission denied for id (824672283)
% 0.22/0.40  ipcrm: permission denied for id (824705052)
% 0.22/0.41  ipcrm: permission denied for id (824770591)
% 0.22/0.41  ipcrm: permission denied for id (824868899)
% 0.22/0.42  ipcrm: permission denied for id (824901669)
% 0.22/0.42  ipcrm: permission denied for id (825098284)
% 0.22/0.43  ipcrm: permission denied for id (825131054)
% 0.22/0.43  ipcrm: permission denied for id (825163823)
% 0.22/0.43  ipcrm: permission denied for id (825229364)
% 0.22/0.45  ipcrm: permission denied for id (825425982)
% 0.22/0.45  ipcrm: permission denied for id (825458751)
% 0.22/0.45  ipcrm: permission denied for id (825524290)
% 0.22/0.47  ipcrm: permission denied for id (825786447)
% 0.22/0.47  ipcrm: permission denied for id (825851985)
% 0.22/0.48  ipcrm: permission denied for id (825950293)
% 0.22/0.48  ipcrm: permission denied for id (825983063)
% 0.22/0.48  ipcrm: permission denied for id (826015832)
% 0.22/0.48  ipcrm: permission denied for id (826048603)
% 0.22/0.49  ipcrm: permission denied for id (826114142)
% 0.22/0.49  ipcrm: permission denied for id (826146911)
% 0.22/0.49  ipcrm: permission denied for id (826179680)
% 0.22/0.49  ipcrm: permission denied for id (826212449)
% 0.22/0.49  ipcrm: permission denied for id (826245218)
% 0.22/0.50  ipcrm: permission denied for id (826310757)
% 0.22/0.51  ipcrm: permission denied for id (826409071)
% 0.22/0.51  ipcrm: permission denied for id (826441841)
% 0.22/0.52  ipcrm: permission denied for id (826540150)
% 0.22/0.52  ipcrm: permission denied for id (826572919)
% 0.22/0.52  ipcrm: permission denied for id (826605688)
% 0.22/0.52  ipcrm: permission denied for id (826703993)
% 0.22/0.53  ipcrm: permission denied for id (826671230)
% 0.87/0.62  % (32460)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.87/0.63  % (32480)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.87/0.64  % (32475)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.09/0.66  % (32467)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.09/0.66  % (32471)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.09/0.67  % (32477)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.09/0.67  % (32464)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.09/0.68  % (32463)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.09/0.68  % (32461)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.09/0.68  % (32472)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.09/0.68  % (32466)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.09/0.68  % (32470)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.09/0.68  % (32469)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.09/0.68  % (32461)Refutation not found, incomplete strategy% (32461)------------------------------
% 1.09/0.68  % (32461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.68  % (32461)Termination reason: Refutation not found, incomplete strategy
% 1.09/0.68  
% 1.09/0.68  % (32461)Memory used [KB]: 10746
% 1.09/0.68  % (32461)Time elapsed: 0.100 s
% 1.09/0.68  % (32461)------------------------------
% 1.09/0.68  % (32461)------------------------------
% 1.09/0.68  % (32459)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.09/0.69  % (32462)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.09/0.69  % (32476)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.09/0.69  % (32474)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.09/0.69  % (32458)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.09/0.69  % (32478)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.09/0.69  % (32468)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.09/0.69  % (32479)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.09/0.69  % (32468)Refutation not found, incomplete strategy% (32468)------------------------------
% 1.09/0.69  % (32468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.69  % (32468)Termination reason: Refutation not found, incomplete strategy
% 1.09/0.69  
% 1.09/0.69  % (32468)Memory used [KB]: 10618
% 1.09/0.69  % (32468)Time elapsed: 0.120 s
% 1.09/0.69  % (32468)------------------------------
% 1.09/0.69  % (32468)------------------------------
% 1.09/0.70  % (32481)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.09/0.70  % (32473)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.09/0.70  % (32481)Refutation not found, incomplete strategy% (32481)------------------------------
% 1.09/0.70  % (32481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.70  % (32481)Termination reason: Refutation not found, incomplete strategy
% 1.09/0.70  
% 1.09/0.70  % (32481)Memory used [KB]: 10746
% 1.09/0.70  % (32481)Time elapsed: 0.122 s
% 1.09/0.70  % (32481)------------------------------
% 1.09/0.70  % (32481)------------------------------
% 1.09/0.70  % (32477)Refutation found. Thanks to Tanya!
% 1.09/0.70  % SZS status Theorem for theBenchmark
% 1.09/0.70  % SZS output start Proof for theBenchmark
% 1.09/0.70  fof(f146,plain,(
% 1.09/0.70    $false),
% 1.09/0.70    inference(subsumption_resolution,[],[f48,f145])).
% 1.09/0.70  fof(f145,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.09/0.70    inference(resolution,[],[f144,f51])).
% 1.09/0.70  fof(f51,plain,(
% 1.09/0.70    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f33,plain,(
% 1.09/0.70    ((((((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))) & m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK4,sK1,sK2) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.09/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f32,f31,f30,f29,f28,f27])).
% 1.09/0.70  fof(f27,plain,(
% 1.09/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(sK0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK0,X1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.09/0.70    introduced(choice_axiom,[])).
% 1.09/0.70  fof(f28,plain,(
% 1.09/0.70    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(sK0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK0,X1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) & v5_pre_topc(X4,sK1,X2) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.09/0.70    introduced(choice_axiom,[])).
% 1.09/0.70  fof(f29,plain,(
% 1.09/0.70    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(sK0,X2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) & v5_pre_topc(X4,sK1,X2) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),X3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X4,sK1,sK2) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.09/0.70    introduced(choice_axiom,[])).
% 1.09/0.70  fof(f30,plain,(
% 1.09/0.70    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),X3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X4,sK1,sK2) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),sK3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X4,sK1,sK2) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.09/0.70    introduced(choice_axiom,[])).
% 1.09/0.70  fof(f31,plain,(
% 1.09/0.70    ? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),sK3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,X4),sK3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X4,sK1,sK2) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),sK3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK4,sK1,sK2) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK4))),
% 1.09/0.70    introduced(choice_axiom,[])).
% 1.09/0.70  fof(f32,plain,(
% 1.09/0.70    ? [X5] : ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),sK3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),X5,sK4),sK3))) & m1_subset_1(k2_tmap_1(sK0,sK1,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X5,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X5,sK3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))) & m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 1.09/0.70    introduced(choice_axiom,[])).
% 1.09/0.70  fof(f12,plain,(
% 1.09/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))) & m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.09/0.70    inference(flattening,[],[f11])).
% 1.09/0.70  fof(f11,plain,(
% 1.09/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))) & (m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X5,X3)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.09/0.70    inference(ennf_transformation,[],[f10])).
% 1.09/0.70  fof(f10,negated_conjecture,(
% 1.09/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))) => (m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) & v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) & v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) & v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))))))))))),
% 1.09/0.70    inference(negated_conjecture,[],[f9])).
% 1.09/0.70  fof(f9,conjecture,(
% 1.09/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X4,X1,X2) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k2_tmap_1(X0,X1,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X5,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X5,X3))) => (m1_subset_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) & v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) & v1_funct_2(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),u1_struct_0(X3),u1_struct_0(X2)) & v1_funct_1(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3))))))))))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tmap_1)).
% 1.09/0.70  fof(f144,plain,(
% 1.09/0.70    ( ! [X6,X4,X5,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f143,f49])).
% 1.09/0.70  fof(f49,plain,(
% 1.09/0.70    v1_funct_1(sK5)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f143,plain,(
% 1.09/0.70    ( ! [X6,X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(sK5)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f140,f45])).
% 1.09/0.70  fof(f45,plain,(
% 1.09/0.70    v1_funct_1(sK4)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f140,plain,(
% 1.09/0.70    ( ! [X6,X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(sK5)) )),
% 1.09/0.70    inference(resolution,[],[f138,f70])).
% 1.09/0.70  fof(f70,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(duplicate_literal_removal,[],[f69])).
% 1.09/0.70  fof(f69,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(superposition,[],[f67,f66])).
% 1.09/0.70  fof(f66,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f24])).
% 1.09/0.70  fof(f24,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.09/0.70    inference(flattening,[],[f23])).
% 1.09/0.70  fof(f23,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.09/0.70    inference(ennf_transformation,[],[f3])).
% 1.09/0.70  fof(f3,axiom,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.09/0.70  fof(f67,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f26])).
% 1.09/0.70  fof(f26,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.09/0.70    inference(flattening,[],[f25])).
% 1.09/0.70  fof(f25,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.09/0.70    inference(ennf_transformation,[],[f1])).
% 1.09/0.70  fof(f1,axiom,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.09/0.70  fof(f138,plain,(
% 1.09/0.70    ~v1_funct_1(k5_relat_1(sK5,sK4))),
% 1.09/0.70    inference(subsumption_resolution,[],[f137,f36])).
% 1.09/0.70  fof(f36,plain,(
% 1.09/0.70    l1_pre_topc(sK0)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f137,plain,(
% 1.09/0.70    ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~l1_pre_topc(sK0)),
% 1.09/0.70    inference(resolution,[],[f136,f44])).
% 1.09/0.70  fof(f44,plain,(
% 1.09/0.70    m1_pre_topc(sK3,sK0)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f136,plain,(
% 1.09/0.70    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~l1_pre_topc(X0)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f135,f39])).
% 1.09/0.70  fof(f39,plain,(
% 1.09/0.70    l1_pre_topc(sK1)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f135,plain,(
% 1.09/0.70    ( ! [X0] : (~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1)) )),
% 1.09/0.70    inference(resolution,[],[f134,f57])).
% 1.09/0.70  fof(f57,plain,(
% 1.09/0.70    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f13])).
% 1.09/0.70  fof(f13,plain,(
% 1.09/0.70    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.09/0.70    inference(ennf_transformation,[],[f4])).
% 1.09/0.70  fof(f4,axiom,(
% 1.09/0.70    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.09/0.70  fof(f134,plain,(
% 1.09/0.70    ( ! [X0] : (~l1_struct_0(sK1) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f133,f37])).
% 1.09/0.70  fof(f37,plain,(
% 1.09/0.70    ~v2_struct_0(sK1)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f133,plain,(
% 1.09/0.70    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(resolution,[],[f132,f59])).
% 1.09/0.70  fof(f59,plain,(
% 1.09/0.70    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f16])).
% 1.09/0.70  fof(f16,plain,(
% 1.09/0.70    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.09/0.70    inference(flattening,[],[f15])).
% 1.09/0.70  fof(f15,plain,(
% 1.09/0.70    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.09/0.70    inference(ennf_transformation,[],[f6])).
% 1.09/0.70  fof(f6,axiom,(
% 1.09/0.70    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.09/0.70  fof(f132,plain,(
% 1.09/0.70    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f131,f50])).
% 1.09/0.70  fof(f50,plain,(
% 1.09/0.70    v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f131,plain,(
% 1.09/0.70    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f130,f46])).
% 1.09/0.70  fof(f46,plain,(
% 1.09/0.70    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f130,plain,(
% 1.09/0.70    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f129,f48])).
% 1.09/0.70  fof(f129,plain,(
% 1.09/0.70    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 1.09/0.70    inference(resolution,[],[f128,f51])).
% 1.09/0.70  fof(f128,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | v1_xboole_0(X1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f127,f49])).
% 1.09/0.70  fof(f127,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | v1_xboole_0(X1) | ~v1_funct_1(sK5)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f126,f45])).
% 1.09/0.70  fof(f126,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | v1_xboole_0(X1) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5)) )),
% 1.09/0.70    inference(condensation,[],[f125])).
% 1.09/0.70  fof(f125,plain,(
% 1.09/0.70    ( ! [X0,X3,X1] : (~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | v1_xboole_0(X1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3))) | ~v1_funct_1(sK5)) )),
% 1.09/0.70    inference(condensation,[],[f124])).
% 1.09/0.70  fof(f124,plain,(
% 1.09/0.70    ( ! [X2,X0,X3,X1] : (~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | v1_xboole_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK2)))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3))) | ~v1_funct_1(sK5)) )),
% 1.09/0.70    inference(resolution,[],[f123,f72])).
% 1.09/0.70  fof(f72,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(duplicate_literal_removal,[],[f71])).
% 1.09/0.70  fof(f71,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(superposition,[],[f68,f66])).
% 1.09/0.70  fof(f68,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f26])).
% 1.09/0.70  fof(f123,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | v1_xboole_0(X1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f122,f49])).
% 1.09/0.70  fof(f122,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | ~v1_funct_1(sK5) | v1_xboole_0(X1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f121,f45])).
% 1.09/0.70  fof(f121,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) | ~v1_funct_2(sK4,X1,u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | ~v1_funct_2(sK5,u1_struct_0(sK0),X1) | ~v1_funct_1(sK5) | v1_xboole_0(X1)) )),
% 1.09/0.70    inference(resolution,[],[f120,f65])).
% 1.09/0.70  fof(f65,plain,(
% 1.09/0.70    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k5_relat_1(X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | v1_xboole_0(X1)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f22])).
% 1.09/0.70  fof(f22,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4] : ((v1_funct_2(k5_relat_1(X3,X4),X0,X2) & v1_funct_1(k5_relat_1(X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | v1_xboole_0(X1))),
% 1.09/0.70    inference(flattening,[],[f21])).
% 1.09/0.70  fof(f21,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4] : ((v1_funct_2(k5_relat_1(X3,X4),X0,X2) & v1_funct_1(k5_relat_1(X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | v1_xboole_0(X1)))),
% 1.09/0.70    inference(ennf_transformation,[],[f2])).
% 1.09/0.70  fof(f2,axiom,(
% 1.09/0.70    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & ~v1_xboole_0(X1)) => (v1_funct_2(k5_relat_1(X3,X4),X0,X2) & v1_funct_1(k5_relat_1(X3,X4))))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).
% 1.09/0.70  fof(f120,plain,(
% 1.09/0.70    ( ! [X0] : (~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) )),
% 1.09/0.70    inference(resolution,[],[f119,f58])).
% 1.09/0.70  fof(f58,plain,(
% 1.09/0.70    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f14])).
% 1.09/0.70  fof(f14,plain,(
% 1.09/0.70    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.09/0.70    inference(ennf_transformation,[],[f5])).
% 1.09/0.70  fof(f5,axiom,(
% 1.09/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.09/0.70  fof(f119,plain,(
% 1.09/0.70    ~l1_pre_topc(sK3) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4))),
% 1.09/0.70    inference(subsumption_resolution,[],[f118,f36])).
% 1.09/0.70  fof(f118,plain,(
% 1.09/0.70    ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.09/0.70    inference(resolution,[],[f117,f57])).
% 1.09/0.70  fof(f117,plain,(
% 1.09/0.70    ~l1_struct_0(sK0) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~l1_pre_topc(sK3)),
% 1.09/0.70    inference(subsumption_resolution,[],[f116,f42])).
% 1.09/0.70  fof(f42,plain,(
% 1.09/0.70    l1_pre_topc(sK2)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f116,plain,(
% 1.09/0.70    ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2)),
% 1.09/0.70    inference(resolution,[],[f115,f57])).
% 1.09/0.70  fof(f115,plain,(
% 1.09/0.70    ~l1_struct_0(sK2) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~l1_struct_0(sK0) | ~l1_pre_topc(sK3)),
% 1.09/0.70    inference(resolution,[],[f114,f57])).
% 1.09/0.70  fof(f114,plain,(
% 1.09/0.70    ~l1_struct_0(sK3) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0)),
% 1.09/0.70    inference(subsumption_resolution,[],[f113,f63])).
% 1.09/0.70  fof(f63,plain,(
% 1.09/0.70    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f20])).
% 1.09/0.70  fof(f20,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.09/0.70    inference(flattening,[],[f19])).
% 1.09/0.70  fof(f19,plain,(
% 1.09/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.09/0.70    inference(ennf_transformation,[],[f7])).
% 1.09/0.70  fof(f7,axiom,(
% 1.09/0.70    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.09/0.70  fof(f113,plain,(
% 1.09/0.70    ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~l1_struct_0(sK3) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0)),
% 1.09/0.70    inference(subsumption_resolution,[],[f112,f61])).
% 1.09/0.70  fof(f61,plain,(
% 1.09/0.70    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f20])).
% 1.09/0.70  fof(f112,plain,(
% 1.09/0.70    ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) | ~l1_struct_0(sK3) | ~m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) | ~v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) | ~v1_funct_1(k5_relat_1(sK5,sK4)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK0)),
% 1.09/0.70    inference(resolution,[],[f107,f62])).
% 1.09/0.70  fof(f62,plain,(
% 1.09/0.70    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.09/0.70    inference(cnf_transformation,[],[f20])).
% 1.09/0.70  fof(f107,plain,(
% 1.09/0.70    ~v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))),
% 1.09/0.70    inference(subsumption_resolution,[],[f77,f106])).
% 1.09/0.70  fof(f106,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f105,f49])).
% 1.09/0.70  fof(f105,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~v1_funct_1(sK5)),
% 1.09/0.70    inference(subsumption_resolution,[],[f104,f51])).
% 1.09/0.70  fof(f104,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK5)),
% 1.09/0.70    inference(subsumption_resolution,[],[f103,f45])).
% 1.09/0.70  fof(f103,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK5)),
% 1.09/0.70    inference(subsumption_resolution,[],[f99,f48])).
% 1.09/0.70  fof(f99,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK5)),
% 1.09/0.70    inference(superposition,[],[f96,f66])).
% 1.09/0.70  fof(f96,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f95,f40])).
% 1.09/0.70  fof(f40,plain,(
% 1.09/0.70    ~v2_struct_0(sK2)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f95,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | v2_struct_0(sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f94,f41])).
% 1.09/0.70  fof(f41,plain,(
% 1.09/0.70    v2_pre_topc(sK2)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f94,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f93,f42])).
% 1.09/0.70  fof(f93,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f92,f45])).
% 1.09/0.70  fof(f92,plain,(
% 1.09/0.70    ~v1_funct_1(sK4) | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f91,f46])).
% 1.09/0.70  fof(f91,plain,(
% 1.09/0.70    ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.09/0.70    inference(subsumption_resolution,[],[f90,f48])).
% 1.09/0.70  fof(f90,plain,(
% 1.09/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.09/0.70    inference(resolution,[],[f89,f47])).
% 1.09/0.70  fof(f47,plain,(
% 1.09/0.70    v5_pre_topc(sK4,sK1,sK2)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f89,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f88,f37])).
% 1.09/0.70  fof(f88,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f87,f38])).
% 1.09/0.70  fof(f38,plain,(
% 1.09/0.70    v2_pre_topc(sK1)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f87,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f86,f39])).
% 1.09/0.70  fof(f86,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f85,f49])).
% 1.09/0.70  fof(f85,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f84,f50])).
% 1.09/0.70  fof(f84,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f83,f51])).
% 1.09/0.70  fof(f83,plain,(
% 1.09/0.70    ( ! [X0,X1] : (~v5_pre_topc(X0,sK1,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X0) | v5_pre_topc(k2_tmap_1(sK0,X1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(X1),sK5,X0),sK3),sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.09/0.70    inference(resolution,[],[f82,f54])).
% 1.09/0.70  fof(f54,plain,(
% 1.09/0.70    v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f82,plain,(
% 1.09/0.70    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0) | ~v5_pre_topc(X2,X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X2) | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f81,f34])).
% 1.09/0.70  fof(f34,plain,(
% 1.09/0.70    ~v2_struct_0(sK0)),
% 1.09/0.70    inference(cnf_transformation,[],[f33])).
% 1.09/0.70  fof(f81,plain,(
% 1.09/0.70    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0) | ~v5_pre_topc(X2,X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X2) | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 1.09/0.70    inference(subsumption_resolution,[],[f80,f35])).
% 1.09/0.71  % (32465)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.09/0.71  % (32480)Refutation not found, incomplete strategy% (32480)------------------------------
% 1.09/0.71  % (32480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.71  % (32480)Termination reason: Refutation not found, incomplete strategy
% 1.09/0.71  
% 1.09/0.71  % (32480)Memory used [KB]: 1791
% 1.09/0.71  % (32480)Time elapsed: 0.109 s
% 1.09/0.71  % (32480)------------------------------
% 1.09/0.71  % (32480)------------------------------
% 1.09/0.72  fof(f35,plain,(
% 1.09/0.72    v2_pre_topc(sK0)),
% 1.09/0.72    inference(cnf_transformation,[],[f33])).
% 1.09/0.72  fof(f80,plain,(
% 1.09/0.72    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0) | ~v5_pre_topc(X2,X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X2) | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.09/0.72    inference(subsumption_resolution,[],[f79,f36])).
% 1.09/0.72  fof(f79,plain,(
% 1.09/0.72    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0) | ~v5_pre_topc(X2,X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X2) | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.09/0.72    inference(subsumption_resolution,[],[f78,f43])).
% 1.09/0.72  fof(f43,plain,(
% 1.09/0.72    ~v2_struct_0(sK3)),
% 1.09/0.72    inference(cnf_transformation,[],[f33])).
% 1.09/0.72  fof(f78,plain,(
% 1.09/0.72    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0) | ~v5_pre_topc(X2,X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X2) | v5_pre_topc(k2_tmap_1(sK0,X3,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X3),X1,X2),sK3),sK3,X3) | v2_struct_0(sK3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.09/0.72    inference(resolution,[],[f60,f44])).
% 1.09/0.72  fof(f60,plain,(
% 1.09/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_pre_topc(X3,X0) | ~v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) | ~v5_pre_topc(X4,X1,X2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X4) | v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f18])).
% 1.09/0.72  fof(f18,plain,(
% 1.09/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | ~v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) | ~v5_pre_topc(X4,X1,X2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.09/0.72    inference(flattening,[],[f17])).
% 1.09/0.72  fof(f17,plain,(
% 1.09/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) | (~v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) | ~v5_pre_topc(X4,X1,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.09/0.72    inference(ennf_transformation,[],[f8])).
% 1.09/0.72  fof(f8,axiom,(
% 1.09/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X5)) => ((v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1) & v5_pre_topc(X4,X1,X2)) => v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2))))))))),
% 1.09/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tmap_1)).
% 1.09/0.72  fof(f77,plain,(
% 1.09/0.72    ~v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))),
% 1.09/0.72    inference(subsumption_resolution,[],[f76,f49])).
% 1.09/0.72  fof(f76,plain,(
% 1.09/0.72    ~v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) | ~v1_funct_1(sK5)),
% 1.09/0.72    inference(subsumption_resolution,[],[f75,f51])).
% 1.09/0.72  fof(f75,plain,(
% 1.09/0.72    ~v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK5)),
% 1.09/0.72    inference(subsumption_resolution,[],[f74,f45])).
% 1.09/0.72  fof(f74,plain,(
% 1.09/0.72    ~v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK5)),
% 1.09/0.72    inference(subsumption_resolution,[],[f73,f48])).
% 1.09/0.72  fof(f73,plain,(
% 1.09/0.72    ~v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK5)),
% 1.09/0.72    inference(superposition,[],[f56,f66])).
% 1.09/0.72  fof(f56,plain,(
% 1.09/0.72    ~v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))),
% 1.09/0.72    inference(cnf_transformation,[],[f33])).
% 1.09/0.72  fof(f48,plain,(
% 1.09/0.72    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.09/0.72    inference(cnf_transformation,[],[f33])).
% 1.09/0.72  % SZS output end Proof for theBenchmark
% 1.09/0.72  % (32477)------------------------------
% 1.09/0.72  % (32477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.72  % (32477)Termination reason: Refutation
% 1.09/0.72  
% 1.09/0.72  % (32477)Memory used [KB]: 6524
% 1.09/0.72  % (32477)Time elapsed: 0.109 s
% 1.09/0.72  % (32477)------------------------------
% 1.09/0.72  % (32477)------------------------------
% 1.09/0.72  % (32324)Success in time 0.356 s
%------------------------------------------------------------------------------

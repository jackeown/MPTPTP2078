%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:16 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  149 (3237 expanded)
%              Number of leaves         :   11 (1671 expanded)
%              Depth                    :   63
%              Number of atoms          : 1611 (85361 expanded)
%              Number of equality atoms :   43 ( 129 expanded)
%              Maximal formula depth    :   31 (  12 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f36])).

fof(f36,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
    & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f22,f21,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                              | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                              | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                            & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X2)
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                          ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1)
                          | ~ v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5)) )
                        & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1)
                        & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                      & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1)
                      & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                    & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1)
                    & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                  & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1)
                  & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,sK2)
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1)
                  | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                  | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5)) )
                & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1)
                & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,sK2)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1)
                | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5)) )
              & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
              & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,sK2)
          & m1_pre_topc(sK2,sK3)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1)
              | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
              | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5)) )
            & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
            & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X4,sK2)
        & m1_pre_topc(sK2,sK3)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1)
            | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1))
            | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5)) )
          & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
          & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK4,sK2)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1)
          | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1))
          | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5)) )
        & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1)
        & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
      & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
      & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X2)
                            & m1_pre_topc(X2,X3) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                               => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X2)
                          & m1_pre_topc(X2,X3) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                             => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_tmap_1)).

fof(f324,plain,(
    ~ m1_pre_topc(sK4,sK0) ),
    inference(resolution,[],[f321,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f40,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5)) ) ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f34,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5)) ) ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK1))
      | v1_funct_1(k3_tmap_1(sK0,sK1,X0,X1,sK5)) ) ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
      | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) ) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) ) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f29,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) ) ),
    inference(resolution,[],[f61,f30])).

fof(f30,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) ) ),
    inference(subsumption_resolution,[],[f60,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f321,plain,(
    ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f247,f320])).

fof(f320,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f319,f25])).

fof(f319,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f318,f26])).

fof(f318,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f317,f27])).

fof(f317,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f316,f28])).

fof(f316,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f315,f29])).

fof(f315,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f314,f30])).

fof(f314,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f313,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f32])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f312,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f311,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f310,f36])).

fof(f310,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f309,f42])).

fof(f42,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f309,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f308,f43])).

fof(f43,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f308,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f307,f44])).

fof(f44,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f307,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f306,f45])).

fof(f45,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f306,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f38])).

fof(f38,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f225,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f49,f205])).

fof(f205,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(subsumption_resolution,[],[f204,f35])).

fof(f204,plain,
    ( v2_struct_0(sK4)
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(subsumption_resolution,[],[f203,f36])).

fof(f203,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(resolution,[],[f190,f38])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ) ),
    inference(subsumption_resolution,[],[f189,f39])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f188,f40])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f187,f41])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f186,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f185,f34])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f184,f31])).

fof(f184,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f183,f32])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f178,f37])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f177,f43])).

fof(f177,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f176,f93])).

fof(f93,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_tmap_1(sK0,sK1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f92,f28])).

fof(f92,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
      | v2_struct_0(sK1)
      | m1_subset_1(k3_tmap_1(sK0,sK1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f89,f29])).

% (22607)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f89,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | m1_subset_1(k3_tmap_1(sK0,sK1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f85,f30])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ) ),
    inference(subsumption_resolution,[],[f84,f25])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f27])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f175,f69])).

fof(f175,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) ) ),
    inference(subsumption_resolution,[],[f174,f25])).

fof(f174,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f26])).

fof(f173,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f27])).

fof(f172,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f28])).

fof(f171,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f29])).

fof(f170,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f30])).

fof(f160,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
      | ~ v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))
      | ~ m1_pre_topc(X5,sK0)
      | ~ m1_pre_topc(X6,sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f157,f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f156,f93])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f155,f69])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f154,f69])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f153,f25])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f152,f26])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f151,f27])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f150,f28])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f149,f29])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f148,f30])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0))
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f132,f93])).

fof(f132,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X4,X1)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0))) ) ),
    inference(subsumption_resolution,[],[f131,f55])).

fof(f131,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X4,X1)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X1,X3,X0),u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0))) ) ),
    inference(subsumption_resolution,[],[f130,f56])).

fof(f130,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X4,X1)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0)
      | ~ m1_subset_1(k3_tmap_1(X5,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X1,X3,X0),u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0))) ) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X4,X1)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0)
      | ~ m1_subset_1(k3_tmap_1(X5,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X1,X3,X0),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k3_tmap_1(X5,X2,X1,X3,X0))
      | ~ m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0))) ) ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
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
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

fof(f247,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f241,f246])).

fof(f246,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) ),
    inference(subsumption_resolution,[],[f245,f25])).

fof(f245,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f26])).

fof(f244,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f27])).

fof(f243,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f242,f32])).

fof(f242,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f219,f36])).

fof(f219,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f113,f205])).

fof(f113,plain,(
    ! [X0] :
      ( v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1)
      | ~ m1_pre_topc(sK4,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,(
    ! [X0] :
      ( v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f111,f38])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f110,f28])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f109,f29])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f107,f31])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f106,f42])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f50,f44])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
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
    inference(cnf_transformation,[],[f12])).

fof(f241,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f46,f240])).

fof(f240,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f239,f43])).

fof(f239,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f238,f45])).

fof(f238,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f237,f32])).

fof(f237,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f236,f36])).

fof(f236,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f218,f42])).

fof(f218,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(superposition,[],[f93,f205])).

fof(f46,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (22598)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (22595)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (22600)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (22610)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (22596)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (22609)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (22616)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (22597)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (22615)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (22617)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (22608)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (22618)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (22602)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (22611)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (22606)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (22599)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (22604)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (22605)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.54  % (22619)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (22601)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (22603)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (22614)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.44/0.54  % (22598)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % (22612)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.44/0.54  % (22601)Refutation not found, incomplete strategy% (22601)------------------------------
% 1.44/0.54  % (22601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (22601)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (22601)Memory used [KB]: 10618
% 1.44/0.54  % (22601)Time elapsed: 0.099 s
% 1.44/0.54  % (22601)------------------------------
% 1.44/0.54  % (22601)------------------------------
% 1.44/0.55  % (22613)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.44/0.55  % (22620)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f325,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(subsumption_resolution,[],[f324,f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    m1_pre_topc(sK4,sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ((((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f22,f21,f20,f19,f18,f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f8,plain,(
% 1.44/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/0.56    inference(flattening,[],[f7])).
% 1.44/0.56  fof(f7,plain,(
% 1.44/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & (m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,negated_conjecture,(
% 1.44/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 1.44/0.56    inference(negated_conjecture,[],[f5])).
% 1.44/0.56  fof(f5,conjecture,(
% 1.44/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_tmap_1)).
% 1.44/0.56  fof(f324,plain,(
% 1.44/0.56    ~m1_pre_topc(sK4,sK0)),
% 1.44/0.56    inference(resolution,[],[f321,f74])).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    ( ! [X0] : (v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,sK0)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f73,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f72,f34])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    m1_pre_topc(sK3,sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))) )),
% 1.44/0.56    inference(resolution,[],[f70,f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f70,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(sK0,sK1,X0,X1,sK5))) )),
% 1.44/0.56    inference(resolution,[],[f69,f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    v1_funct_1(sK5)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f69,plain,(
% 1.44/0.56    ( ! [X4,X5,X3] : (~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f68,f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ~v2_struct_0(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f68,plain,(
% 1.44/0.56    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f65,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    v2_pre_topc(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f65,plain,(
% 1.44/0.56    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) )),
% 1.44/0.56    inference(resolution,[],[f61,f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    l1_pre_topc(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f61,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X2) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f60,f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ~v2_struct_0(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) | v2_struct_0(sK0)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f58,f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    v2_pre_topc(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.44/0.56    inference(resolution,[],[f54,f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    l1_pre_topc(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.56    inference(flattening,[],[f15])).
% 1.57/0.56  fof(f15,plain,(
% 1.57/0.56    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f2])).
% 1.57/0.56  fof(f2,axiom,(
% 1.57/0.56    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.57/0.56  fof(f321,plain,(
% 1.57/0.56    ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 1.57/0.56    inference(subsumption_resolution,[],[f247,f320])).
% 1.57/0.56  fof(f320,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.57/0.56    inference(subsumption_resolution,[],[f319,f25])).
% 1.57/0.56  fof(f319,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f318,f26])).
% 1.57/0.56  fof(f318,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f317,f27])).
% 1.57/0.56  fof(f317,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f316,f28])).
% 1.57/0.56  fof(f316,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f315,f29])).
% 1.57/0.56  fof(f315,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f314,f30])).
% 1.57/0.56  fof(f314,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f313,f31])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    ~v2_struct_0(sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f313,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f312,f32])).
% 1.57/0.56  fof(f32,plain,(
% 1.57/0.56    m1_pre_topc(sK2,sK0)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f312,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f311,f35])).
% 1.57/0.56  fof(f35,plain,(
% 1.57/0.56    ~v2_struct_0(sK4)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f311,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f310,f36])).
% 1.57/0.56  fof(f310,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f309,f42])).
% 1.57/0.56  fof(f42,plain,(
% 1.57/0.56    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f309,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f308,f43])).
% 1.57/0.56  fof(f43,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f308,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f307,f44])).
% 1.57/0.56  fof(f44,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f307,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f306,f45])).
% 1.57/0.56  fof(f45,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f306,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f225,f38])).
% 1.57/0.56  fof(f38,plain,(
% 1.57/0.56    m1_pre_topc(sK4,sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f225,plain,(
% 1.57/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK2) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(superposition,[],[f49,f205])).
% 1.57/0.56  fof(f205,plain,(
% 1.57/0.56    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 1.57/0.56    inference(subsumption_resolution,[],[f204,f35])).
% 1.57/0.56  fof(f204,plain,(
% 1.57/0.56    v2_struct_0(sK4) | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 1.57/0.56    inference(subsumption_resolution,[],[f203,f36])).
% 1.57/0.56  fof(f203,plain,(
% 1.57/0.56    ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 1.57/0.56    inference(resolution,[],[f190,f38])).
% 1.57/0.56  fof(f190,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f189,f39])).
% 1.57/0.56  fof(f189,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f188,f40])).
% 1.57/0.56  fof(f188,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f187,f41])).
% 1.57/0.56  fof(f187,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f186,f33])).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    ~v2_struct_0(sK3)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f186,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f185,f34])).
% 1.57/0.56  fof(f185,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f184,f31])).
% 1.57/0.56  fof(f184,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f183,f32])).
% 1.57/0.56  fof(f183,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f178,f37])).
% 1.57/0.56  fof(f37,plain,(
% 1.57/0.56    m1_pre_topc(sK2,sK3)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f178,plain,(
% 1.57/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | k3_tmap_1(sK0,sK1,sK3,X0,sK5) = k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5)) )),
% 1.57/0.56    inference(resolution,[],[f177,f43])).
% 1.57/0.56  fof(f177,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_1(X4)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f176,f93])).
% 1.57/0.56  fof(f93,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (m1_subset_1(k3_tmap_1(sK0,sK1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f92,f28])).
% 1.57/0.56  fof(f92,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f89,f29])).
% 1.57/0.56  % (22607)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.57/0.56  fof(f89,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | m1_subset_1(k3_tmap_1(sK0,sK1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))) )),
% 1.57/0.56    inference(resolution,[],[f85,f30])).
% 1.57/0.56  fof(f85,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X2) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | v2_struct_0(X2) | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f84,f25])).
% 1.57/0.56  fof(f84,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f82,f26])).
% 1.57/0.56  fof(f82,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | m1_subset_1(k3_tmap_1(sK0,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(resolution,[],[f56,f27])).
% 1.57/0.56  fof(f56,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f16])).
% 1.57/0.56  fof(f176,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f175,f69])).
% 1.57/0.56  fof(f175,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f174,f25])).
% 1.57/0.56  fof(f174,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f173,f26])).
% 1.57/0.56  fof(f173,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f172,f27])).
% 1.57/0.56  fof(f172,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f171,f28])).
% 1.57/0.56  fof(f171,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f170,f29])).
% 1.57/0.56  fof(f170,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f160,f30])).
% 1.57/0.56  fof(f160,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(duplicate_literal_removal,[],[f159])).
% 1.57/0.56  fof(f159,plain,(
% 1.57/0.56    ( ! [X6,X4,X7,X5] : (~v1_funct_1(X4) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | k3_tmap_1(sK0,sK1,X7,X5,X4) = k3_tmap_1(sK0,sK1,X6,X5,k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(X4,u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X7,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X7,X6,X4),u1_struct_0(X6),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X7,X6,X4)) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X6,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.56    inference(resolution,[],[f157,f55])).
% 1.57/0.56  fof(f55,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f16])).
% 1.57/0.56  fof(f157,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f156,f93])).
% 1.57/0.56  fof(f156,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f155,f69])).
% 1.57/0.56  fof(f155,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f154,f69])).
% 1.57/0.56  fof(f154,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f153,f25])).
% 1.57/0.56  fof(f153,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f152,f26])).
% 1.57/0.56  fof(f152,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f151,f27])).
% 1.57/0.56  fof(f151,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f150,f28])).
% 1.57/0.56  fof(f150,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f149,f29])).
% 1.57/0.56  fof(f149,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f148,f30])).
% 1.57/0.56  fof(f148,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(duplicate_literal_removal,[],[f147])).
% 1.57/0.56  fof(f147,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0)),u1_struct_0(X2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,X1,X3,X0))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X1,X3,X0)) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK0) | ~m1_subset_1(k3_tmap_1(sK0,sK1,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X1,X3,X0),u1_struct_0(X3),u1_struct_0(sK1))) )),
% 1.57/0.56    inference(resolution,[],[f132,f93])).
% 1.57/0.56  fof(f132,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X4,X1) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~m1_pre_topc(X1,X5) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f131,f55])).
% 1.57/0.56  fof(f131,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X4,X1) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~m1_pre_topc(X1,X5) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0) | ~v1_funct_2(k3_tmap_1(X5,X2,X1,X3,X0),u1_struct_0(X3),u1_struct_0(X2)) | ~m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f130,f56])).
% 1.57/0.56  fof(f130,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X4,X1) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~m1_pre_topc(X1,X5) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0) | ~m1_subset_1(k3_tmap_1(X5,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k3_tmap_1(X5,X2,X1,X3,X0),u1_struct_0(X3),u1_struct_0(X2)) | ~m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f129,f54])).
% 1.57/0.56  fof(f129,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X4,X1) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~m1_pre_topc(X1,X5) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)) = k3_tmap_1(X5,X2,X1,X3,X0) | ~m1_subset_1(k3_tmap_1(X5,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k3_tmap_1(X5,X2,X1,X3,X0),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k3_tmap_1(X5,X2,X1,X3,X0)) | ~m1_subset_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k3_tmap_1(X5,X2,X4,X3,k3_tmap_1(X5,X2,X1,X4,X0)))) )),
% 1.57/0.56    inference(resolution,[],[f47,f52])).
% 1.57/0.56  fof(f52,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f24,plain,(
% 1.57/0.56    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.56    inference(nnf_transformation,[],[f14])).
% 1.57/0.56  fof(f14,plain,(
% 1.57/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.56    inference(flattening,[],[f13])).
% 1.57/0.56  fof(f13,plain,(
% 1.57/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.56    inference(ennf_transformation,[],[f1])).
% 1.57/0.56  fof(f1,axiom,(
% 1.57/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.57/0.56  fof(f47,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f10])).
% 1.57/0.56  fof(f10,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f9])).
% 1.57/0.56  fof(f9,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f3])).
% 1.57/0.56  fof(f3,axiom,(
% 1.57/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).
% 1.57/0.56  fof(f49,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f12,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f11])).
% 1.57/0.56  fof(f11,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f4])).
% 1.57/0.56  fof(f4,axiom,(
% 1.57/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).
% 1.57/0.56  fof(f247,plain,(
% 1.57/0.56    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 1.57/0.56    inference(subsumption_resolution,[],[f241,f246])).
% 1.57/0.56  fof(f246,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)),
% 1.57/0.56    inference(subsumption_resolution,[],[f245,f25])).
% 1.57/0.56  fof(f245,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f244,f26])).
% 1.57/0.56  fof(f244,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f243,f27])).
% 1.57/0.56  fof(f243,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f242,f32])).
% 1.57/0.56  fof(f242,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f219,f36])).
% 1.57/0.56  fof(f219,plain,(
% 1.57/0.56    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(superposition,[],[f113,f205])).
% 1.57/0.56  fof(f113,plain,(
% 1.57/0.56    ( ! [X0] : (v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1) | ~m1_pre_topc(sK4,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f112,f35])).
% 1.57/0.56  fof(f112,plain,(
% 1.57/0.56    ( ! [X0] : (v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(resolution,[],[f111,f38])).
% 1.57/0.56  fof(f111,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f110,f28])).
% 1.57/0.56  fof(f110,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f109,f29])).
% 1.57/0.56  fof(f109,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f108,f30])).
% 1.57/0.56  fof(f108,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f107,f31])).
% 1.57/0.56  fof(f107,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f106,f42])).
% 1.57/0.56  fof(f106,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f105,f43])).
% 1.57/0.56  fof(f105,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f104,f45])).
% 1.57/0.56  fof(f104,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v5_pre_topc(k3_tmap_1(X1,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),X0,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.57/0.56    inference(resolution,[],[f50,f44])).
% 1.57/0.56  fof(f50,plain,(
% 1.57/0.56    ( ! [X4,X2,X0,X3,X1] : (~v5_pre_topc(X4,X2,X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f241,plain,(
% 1.57/0.56    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 1.57/0.56    inference(subsumption_resolution,[],[f46,f240])).
% 1.57/0.56  fof(f240,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.57/0.56    inference(subsumption_resolution,[],[f239,f43])).
% 1.57/0.56  fof(f239,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.57/0.56    inference(subsumption_resolution,[],[f238,f45])).
% 1.57/0.56  fof(f238,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.57/0.56    inference(subsumption_resolution,[],[f237,f32])).
% 1.57/0.56  fof(f237,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.57/0.56    inference(subsumption_resolution,[],[f236,f36])).
% 1.57/0.56  fof(f236,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.57/0.56    inference(subsumption_resolution,[],[f218,f42])).
% 1.57/0.56  fof(f218,plain,(
% 1.57/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.57/0.56    inference(superposition,[],[f93,f205])).
% 1.57/0.56  fof(f46,plain,(
% 1.57/0.56    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (22598)------------------------------
% 1.57/0.56  % (22598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (22598)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (22598)Memory used [KB]: 6652
% 1.57/0.56  % (22598)Time elapsed: 0.123 s
% 1.57/0.56  % (22598)------------------------------
% 1.57/0.56  % (22598)------------------------------
% 1.57/0.57  % (22594)Success in time 0.206 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:19:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  299 (25471 expanded)
%              Number of leaves         :   17 (12941 expanded)
%              Depth                    :   68
%              Number of atoms          : 1995 (632781 expanded)
%              Number of equality atoms :   91 (1596 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f806,plain,(
    $false ),
    inference(subsumption_resolution,[],[f805,f54])).

fof(f54,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f38,f37,f36,f35,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).

fof(f805,plain,(
    ~ m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f804,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f804,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f801,f521])).

fof(f521,plain,(
    ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f480,f520])).

fof(f520,plain,(
    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f519,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f519,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f518,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f518,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f517,f43])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f517,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f516,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f516,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f515,f45])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f515,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f514,f46])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f514,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f513,f50])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f513,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f512,f52])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f512,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f511,f55])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f511,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f510,f56])).

fof(f56,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f510,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f509,f57])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f509,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f76,f474])).

fof(f474,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4) ),
    inference(forward_demodulation,[],[f445,f185])).

fof(f185,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f175,f139])).

fof(f139,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(resolution,[],[f137,f54])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f122,f53])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f122,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X6,X7)
      | m1_pre_topc(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f117,f99])).

fof(f99,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f96,f50])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f68,f42])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f117,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X7,sK3)
      | m1_pre_topc(X6,sK3)
      | ~ v2_pre_topc(sK3) ) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f79,f50])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f174,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f173,f99])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f172,f82])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f171,f44])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f170,f45])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f169,f46])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f168,f55])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f166,f56])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f67,f57])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f445,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f250,f139])).

fof(f250,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5) ) ),
    inference(subsumption_resolution,[],[f249,f41])).

fof(f249,plain,(
    ! [X1] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f248,f42])).

fof(f248,plain,(
    ! [X1] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5)
      | ~ m1_pre_topc(X1,sK3)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f243,f43])).

fof(f243,plain,(
    ! [X1] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5)
      | ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f232,f50])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f231,f69])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f230,f44])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f229,f45])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f228,f46])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f227,f55])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f223,f56])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f65,f57])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f480,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) ),
    inference(forward_demodulation,[],[f479,f474])).

fof(f479,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f478,f421])).

fof(f421,plain,(
    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f420,f82])).

fof(f420,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f334,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f334,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f333,f49])).

fof(f333,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f332,f99])).

fof(f332,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f331,f82])).

fof(f331,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f330,f44])).

fof(f330,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f329,f45])).

fof(f329,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f328,f46])).

fof(f328,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f327,f139])).

fof(f327,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f326,f55])).

fof(f326,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f325,f56])).

fof(f325,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f319,f57])).

fof(f319,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f77,f255])).

fof(f255,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK3,sK1,sK3,sK4,sK5) ),
    inference(forward_demodulation,[],[f252,f185])).

fof(f252,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK3,sK1,sK3,sK4,sK5) ),
    inference(resolution,[],[f247,f139])).

fof(f247,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f246,f49])).

fof(f246,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f245,f99])).

fof(f245,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f244,f82])).

fof(f244,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f232,f63])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f32])).

fof(f478,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f477,f474])).

fof(f477,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f476,f474])).

fof(f476,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f475,f346])).

fof(f346,plain,(
    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f345,f82])).

fof(f345,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f324,f63])).

fof(f324,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f323,f49])).

fof(f323,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f322,f99])).

fof(f322,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f321,f82])).

fof(f321,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f318,f139])).

fof(f318,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f153,f255])).

fof(f153,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f151,f45])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f150,f46])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f149,f56])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f147,f57])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK5))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X0,X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f475,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f62,f474])).

fof(f62,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f801,plain,
    ( v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2) ),
    inference(superposition,[],[f456,f766])).

fof(f766,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) ),
    inference(subsumption_resolution,[],[f765,f54])).

fof(f765,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f764,f51])).

fof(f764,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f761,f453])).

fof(f453,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(backward_demodulation,[],[f164,f447])).

fof(f447,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2) ),
    inference(forward_demodulation,[],[f444,f184])).

fof(f184,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f175,f53])).

fof(f444,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f250,f53])).

fof(f164,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f163,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f162,f98])).

fof(f98,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f96,f48])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f161,f81])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f79,f48])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f160,f44])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f159,f45])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f157,f58])).

fof(f58,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f156,f59])).

fof(f59,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f155,f61])).

fof(f61,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f761,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) ),
    inference(subsumption_resolution,[],[f725,f757])).

fof(f757,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f756,f41])).

fof(f756,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f755,f42])).

fof(f755,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f754,f43])).

fof(f754,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f753,f44])).

fof(f753,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f752,f45])).

fof(f752,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f751,f46])).

fof(f751,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f750,f48])).

fof(f750,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f749,f52])).

fof(f749,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f748,f286])).

fof(f286,plain,(
    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f285,f82])).

fof(f285,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f264,f63])).

fof(f264,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f263,f49])).

fof(f263,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f262,f99])).

fof(f262,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f261,f82])).

fof(f261,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f258,f53])).

fof(f258,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f153,f254])).

fof(f254,plain,(
    k2_tmap_1(sK3,sK1,sK5,sK2) = k3_tmap_1(sK3,sK1,sK3,sK2,sK5) ),
    inference(forward_demodulation,[],[f251,f184])).

fof(f251,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK5) ),
    inference(resolution,[],[f247,f53])).

fof(f748,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f747,f449])).

fof(f449,plain,(
    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f59,f447])).

fof(f747,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f746,f373])).

fof(f373,plain,(
    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f372,f82])).

fof(f372,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f274,f63])).

fof(f274,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f273,f49])).

fof(f273,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f272,f99])).

fof(f272,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f271,f82])).

fof(f271,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f270,f44])).

fof(f270,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f269,f45])).

fof(f269,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f268,f46])).

fof(f268,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f267,f53])).

fof(f267,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f266,f55])).

fof(f266,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f265,f56])).

fof(f265,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f259,f57])).

fof(f259,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f77,f254])).

fof(f746,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f76,f686])).

fof(f686,plain,(
    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f685,f41])).

fof(f685,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f684,f42])).

fof(f684,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f678,f43])).

fof(f678,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f674,f48])).

fof(f674,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f672,f459])).

fof(f459,plain,(
    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4)) ),
    inference(backward_demodulation,[],[f214,f447])).

fof(f214,plain,(
    k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) ),
    inference(resolution,[],[f183,f54])).

fof(f183,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f182,f47])).

fof(f182,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f181,f98])).

fof(f181,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f180,f81])).

fof(f180,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f179,f44])).

fof(f179,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f178,f45])).

fof(f178,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f177,f46])).

fof(f177,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f176,f58])).

fof(f176,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f167,f59])).

fof(f167,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f67,f61])).

fof(f672,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4)) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f464,f54])).

fof(f464,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f388,f449])).

fof(f388,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f387,f69])).

fof(f387,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f386,f44])).

fof(f386,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK2,X4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f385,f45])).

fof(f385,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK2,X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f384,f46])).

fof(f384,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f375,f286])).

fof(f375,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3))
      | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f373,f65])).

fof(f725,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(subsumption_resolution,[],[f691,f724])).

fof(f724,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f723,f81])).

fof(f723,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f712,f63])).

fof(f712,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f711,f47])).

fof(f711,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f710,f98])).

fof(f710,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f709,f81])).

fof(f709,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f708,f44])).

fof(f708,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f707,f45])).

fof(f707,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f706,f46])).

fof(f706,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f705,f54])).

fof(f705,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f704,f286])).

fof(f704,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f703,f449])).

fof(f703,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f701,f373])).

fof(f701,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f77,f683])).

fof(f683,plain,(
    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) ),
    inference(subsumption_resolution,[],[f682,f47])).

fof(f682,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f681,f98])).

fof(f681,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f680,f81])).

fof(f680,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f677])).

fof(f677,plain,
    ( k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f674,f63])).

fof(f691,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) ),
    inference(forward_demodulation,[],[f690,f686])).

fof(f690,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f689,f686])).

fof(f689,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f687,f686])).

fof(f687,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))
    | k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f637,f686])).

fof(f637,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))) ),
    inference(subsumption_resolution,[],[f636,f346])).

fof(f636,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))) ),
    inference(subsumption_resolution,[],[f635,f520])).

fof(f635,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))) ),
    inference(subsumption_resolution,[],[f634,f421])).

fof(f634,plain,
    ( k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))) ),
    inference(resolution,[],[f630,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f630,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k2_tmap_1(sK3,sK1,sK5,sK4)) ),
    inference(forward_demodulation,[],[f629,f474])).

fof(f629,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f627,f51])).

fof(f627,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f606,f54])).

fof(f606,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),k3_tmap_1(sK0,sK1,sK3,X0,sK5))
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f605,f447])).

fof(f605,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,X0,sK5)) ) ),
    inference(subsumption_resolution,[],[f602,f47])).

fof(f602,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK2)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,X0,sK5)) ) ),
    inference(resolution,[],[f538,f53])).

fof(f538,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5)) ) ),
    inference(subsumption_resolution,[],[f537,f41])).

fof(f537,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f536,f42])).

fof(f536,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f531,f43])).

fof(f531,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f359,f50])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f358,f69])).

fof(f358,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f357,f69])).

fof(f357,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f356,f44])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f355,f45])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f354,f46])).

fof(f354,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f353,f49])).

fof(f353,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f352,f55])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f348,f56])).

fof(f348,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f456,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),X0),X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(backward_demodulation,[],[f197,f447])).

fof(f197,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f196,f47])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f195,f98])).

fof(f195,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f194,f81])).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f193,f44])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f192,f45])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f191,f46])).

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f190,f58])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f189,f59])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f188,f61])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f72,f60])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (11470)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (11471)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (11486)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (11485)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (11469)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (11482)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (11468)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (11490)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (11479)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (11474)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (11476)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (11477)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (11480)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (11487)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (11472)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (11488)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (11489)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (11473)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (11475)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (11478)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (11467)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (11492)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (11481)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (11484)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (11491)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (11483)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.61  % (11470)Refutation found. Thanks to Tanya!
% 0.22/0.61  % SZS status Theorem for theBenchmark
% 0.22/0.61  % SZS output start Proof for theBenchmark
% 0.22/0.61  fof(f806,plain,(
% 0.22/0.61    $false),
% 0.22/0.61    inference(subsumption_resolution,[],[f805,f54])).
% 0.22/0.61  fof(f54,plain,(
% 0.22/0.61    m1_pre_topc(sK4,sK2)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f39,plain,(
% 0.22/0.61    ((((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f38,f37,f36,f35,f34,f33])).
% 0.22/0.61  fof(f33,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f34,plain,(
% 0.22/0.61    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f35,plain,(
% 0.22/0.61    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f36,plain,(
% 0.22/0.61    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,X3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f37,plain,(
% 0.22/0.61    ? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f38,plain,(
% 0.22/0.61    ? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,X5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,X5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,X5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,X5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f14,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f13])).
% 0.22/0.61  fof(f13,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & (m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f12])).
% 0.22/0.61  fof(f12,negated_conjecture,(
% 0.22/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 0.22/0.61    inference(negated_conjecture,[],[f11])).
% 0.22/0.61  fof(f11,conjecture,(
% 0.22/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).
% 0.22/0.61  fof(f805,plain,(
% 0.22/0.61    ~m1_pre_topc(sK4,sK2)),
% 0.22/0.61    inference(subsumption_resolution,[],[f804,f51])).
% 0.22/0.61  fof(f51,plain,(
% 0.22/0.61    ~v2_struct_0(sK4)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f804,plain,(
% 0.22/0.61    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2)),
% 0.22/0.61    inference(subsumption_resolution,[],[f801,f521])).
% 0.22/0.61  fof(f521,plain,(
% 0.22/0.61    ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)),
% 0.22/0.61    inference(subsumption_resolution,[],[f480,f520])).
% 0.22/0.61  fof(f520,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f519,f41])).
% 0.22/0.61  fof(f41,plain,(
% 0.22/0.61    ~v2_struct_0(sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f519,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f518,f42])).
% 0.22/0.61  fof(f42,plain,(
% 0.22/0.61    v2_pre_topc(sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f518,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f517,f43])).
% 0.22/0.61  fof(f43,plain,(
% 0.22/0.61    l1_pre_topc(sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f517,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f516,f44])).
% 0.22/0.61  fof(f44,plain,(
% 0.22/0.61    ~v2_struct_0(sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f516,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f515,f45])).
% 0.22/0.61  fof(f45,plain,(
% 0.22/0.61    v2_pre_topc(sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f515,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f514,f46])).
% 0.22/0.61  fof(f46,plain,(
% 0.22/0.61    l1_pre_topc(sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f514,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f513,f50])).
% 0.22/0.61  fof(f50,plain,(
% 0.22/0.61    m1_pre_topc(sK3,sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f513,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f512,f52])).
% 0.22/0.61  fof(f52,plain,(
% 0.22/0.61    m1_pre_topc(sK4,sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f512,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f511,f55])).
% 0.22/0.61  fof(f55,plain,(
% 0.22/0.61    v1_funct_1(sK5)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f511,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f510,f56])).
% 0.22/0.61  fof(f56,plain,(
% 0.22/0.61    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f510,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f509,f57])).
% 0.22/0.61  fof(f57,plain,(
% 0.22/0.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f509,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(superposition,[],[f76,f474])).
% 0.22/0.61  fof(f474,plain,(
% 0.22/0.61    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_tmap_1(sK3,sK1,sK5,sK4)),
% 0.22/0.61    inference(forward_demodulation,[],[f445,f185])).
% 0.22/0.61  fof(f185,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 0.22/0.61    inference(resolution,[],[f175,f139])).
% 0.22/0.61  fof(f139,plain,(
% 0.22/0.61    m1_pre_topc(sK4,sK3)),
% 0.22/0.61    inference(resolution,[],[f137,f54])).
% 0.22/0.61  fof(f137,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK3)) )),
% 0.22/0.61    inference(resolution,[],[f122,f53])).
% 0.22/0.61  fof(f53,plain,(
% 0.22/0.61    m1_pre_topc(sK2,sK3)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f122,plain,(
% 0.22/0.61    ( ! [X6,X7] : (~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,X7) | m1_pre_topc(X6,sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f117,f99])).
% 0.22/0.61  fof(f99,plain,(
% 0.22/0.61    v2_pre_topc(sK3)),
% 0.22/0.61    inference(resolution,[],[f96,f50])).
% 0.22/0.61  fof(f96,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f94,f43])).
% 0.22/0.61  fof(f94,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(X0)) )),
% 0.22/0.61    inference(resolution,[],[f68,f42])).
% 0.22/0.61  fof(f68,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f24])).
% 0.22/0.61  fof(f24,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.61    inference(flattening,[],[f23])).
% 0.22/0.61  fof(f23,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f2])).
% 0.22/0.61  fof(f2,axiom,(
% 0.22/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.61  fof(f117,plain,(
% 0.22/0.61    ( ! [X6,X7] : (~m1_pre_topc(X6,X7) | ~m1_pre_topc(X7,sK3) | m1_pre_topc(X6,sK3) | ~v2_pre_topc(sK3)) )),
% 0.22/0.61    inference(resolution,[],[f69,f82])).
% 0.22/0.61  fof(f82,plain,(
% 0.22/0.61    l1_pre_topc(sK3)),
% 0.22/0.61    inference(resolution,[],[f79,f50])).
% 0.22/0.61  fof(f79,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.22/0.61    inference(resolution,[],[f64,f43])).
% 0.22/0.61  fof(f64,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f16])).
% 0.22/0.61  fof(f16,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f3])).
% 0.22/0.61  fof(f3,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.61  fof(f69,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f26])).
% 0.22/0.61  fof(f26,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.61    inference(flattening,[],[f25])).
% 0.22/0.61  fof(f25,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f10])).
% 0.22/0.61  fof(f10,axiom,(
% 0.22/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.61  fof(f175,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f174,f49])).
% 0.22/0.61  fof(f49,plain,(
% 0.22/0.61    ~v2_struct_0(sK3)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f174,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f173,f99])).
% 0.22/0.61  fof(f173,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f172,f82])).
% 0.22/0.61  fof(f172,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f171,f44])).
% 0.22/0.61  fof(f171,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f170,f45])).
% 0.22/0.61  fof(f170,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f169,f46])).
% 0.22/0.61  fof(f169,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f168,f55])).
% 0.22/0.61  fof(f168,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f166,f56])).
% 0.22/0.61  fof(f166,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(resolution,[],[f67,f57])).
% 0.22/0.61  fof(f67,plain,(
% 0.22/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f22])).
% 0.22/0.61  fof(f22,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f21])).
% 0.22/0.61  fof(f21,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f4])).
% 0.22/0.61  fof(f4,axiom,(
% 0.22/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.61  fof(f445,plain,(
% 0.22/0.61    k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 0.22/0.61    inference(resolution,[],[f250,f139])).
% 0.22/0.61  fof(f250,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f249,f41])).
% 0.22/0.61  fof(f249,plain,(
% 0.22/0.61    ( ! [X1] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5) | ~m1_pre_topc(X1,sK3) | v2_struct_0(sK0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f248,f42])).
% 0.22/0.61  fof(f248,plain,(
% 0.22/0.61    ( ! [X1] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f243,f43])).
% 0.22/0.61  fof(f243,plain,(
% 0.22/0.61    ( ! [X1] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X1)) = k3_tmap_1(sK0,sK1,sK3,X1,sK5) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.61    inference(resolution,[],[f232,f50])).
% 0.22/0.61  fof(f232,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f231,f69])).
% 0.22/0.61  fof(f231,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f230,f44])).
% 0.22/0.61  fof(f230,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f229,f45])).
% 0.22/0.61  fof(f229,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f228,f46])).
% 0.22/0.61  fof(f228,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f227,f55])).
% 0.22/0.61  fof(f227,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f223,f56])).
% 0.22/0.61  fof(f223,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.61    inference(resolution,[],[f65,f57])).
% 0.22/0.61  fof(f65,plain,(
% 0.22/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f18])).
% 0.22/0.61  fof(f18,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f17])).
% 0.22/0.61  fof(f17,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f5])).
% 0.22/0.61  fof(f5,axiom,(
% 0.22/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.61  fof(f76,plain,(
% 0.22/0.61    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f32,plain,(
% 0.22/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f31])).
% 0.22/0.61  fof(f31,plain,(
% 0.22/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f6])).
% 0.22/0.61  fof(f6,axiom,(
% 0.22/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 0.22/0.61  fof(f480,plain,(
% 0.22/0.61    ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1)),
% 0.22/0.61    inference(forward_demodulation,[],[f479,f474])).
% 0.22/0.61  fof(f479,plain,(
% 0.22/0.61    ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f478,f421])).
% 0.22/0.61  fof(f421,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.61    inference(subsumption_resolution,[],[f420,f82])).
% 0.22/0.61  fof(f420,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK3)),
% 0.22/0.61    inference(resolution,[],[f334,f63])).
% 0.22/0.61  fof(f63,plain,(
% 0.22/0.61    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f15])).
% 0.22/0.61  fof(f15,plain,(
% 0.22/0.61    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f8])).
% 0.22/0.61  fof(f8,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.61  fof(f334,plain,(
% 0.22/0.61    ~m1_pre_topc(sK3,sK3) | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.61    inference(subsumption_resolution,[],[f333,f49])).
% 0.22/0.61  fof(f333,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f332,f99])).
% 0.22/0.61  fof(f332,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f331,f82])).
% 0.22/0.61  fof(f331,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f330,f44])).
% 0.22/0.61  fof(f330,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f329,f45])).
% 0.22/0.61  fof(f329,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f328,f46])).
% 0.22/0.61  fof(f328,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f327,f139])).
% 0.22/0.61  fof(f327,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f326,f55])).
% 0.22/0.61  fof(f326,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f325,f56])).
% 0.22/0.61  fof(f325,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f319,f57])).
% 0.22/0.61  fof(f319,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(superposition,[],[f77,f255])).
% 0.22/0.61  fof(f255,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK3,sK1,sK3,sK4,sK5)),
% 0.22/0.61    inference(forward_demodulation,[],[f252,f185])).
% 0.22/0.61  fof(f252,plain,(
% 0.22/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK3,sK1,sK3,sK4,sK5)),
% 0.22/0.61    inference(resolution,[],[f247,f139])).
% 0.22/0.61  fof(f247,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f246,f49])).
% 0.22/0.61  fof(f246,plain,(
% 0.22/0.61    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f245,f99])).
% 0.22/0.61  fof(f245,plain,(
% 0.22/0.61    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f244,f82])).
% 0.22/0.61  fof(f244,plain,(
% 0.22/0.61    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f242])).
% 0.22/0.61  fof(f242,plain,(
% 0.22/0.61    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK5) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK3)) )),
% 0.22/0.61    inference(resolution,[],[f232,f63])).
% 0.22/0.61  fof(f77,plain,(
% 0.22/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f478,plain,(
% 0.22/0.61    ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(forward_demodulation,[],[f477,f474])).
% 0.22/0.61  fof(f477,plain,(
% 0.22/0.61    ~v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(forward_demodulation,[],[f476,f474])).
% 0.22/0.61  fof(f476,plain,(
% 0.22/0.61    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f475,f346])).
% 0.22/0.61  fof(f346,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))),
% 0.22/0.61    inference(subsumption_resolution,[],[f345,f82])).
% 0.22/0.61  fof(f345,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~l1_pre_topc(sK3)),
% 0.22/0.61    inference(resolution,[],[f324,f63])).
% 0.22/0.61  fof(f324,plain,(
% 0.22/0.61    ~m1_pre_topc(sK3,sK3) | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4))),
% 0.22/0.61    inference(subsumption_resolution,[],[f323,f49])).
% 0.22/0.61  fof(f323,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f322,f99])).
% 0.22/0.61  fof(f322,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f321,f82])).
% 0.22/0.61  fof(f321,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f318,f139])).
% 0.22/0.61  fof(f318,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(superposition,[],[f153,f255])).
% 0.22/0.61  fof(f153,plain,(
% 0.22/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f152,f44])).
% 0.22/0.61  fof(f152,plain,(
% 0.22/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f151,f45])).
% 0.22/0.61  fof(f151,plain,(
% 0.22/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f150,f46])).
% 0.22/0.61  fof(f150,plain,(
% 0.22/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f149,f56])).
% 0.22/0.61  fof(f149,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(resolution,[],[f147,f57])).
% 0.22/0.61  fof(f147,plain,(
% 0.22/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK5)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.22/0.61    inference(resolution,[],[f75,f55])).
% 0.22/0.61  fof(f75,plain,(
% 0.22/0.61    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f475,plain,(
% 0.22/0.61    ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(backward_demodulation,[],[f62,f474])).
% 0.22/0.61  fof(f62,plain,(
% 0.22/0.61    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f801,plain,(
% 0.22/0.61    v5_pre_topc(k2_tmap_1(sK3,sK1,sK5,sK4),sK4,sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2)),
% 0.22/0.61    inference(superposition,[],[f456,f766])).
% 0.22/0.61  fof(f766,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)),
% 0.22/0.61    inference(subsumption_resolution,[],[f765,f54])).
% 0.22/0.61  fof(f765,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~m1_pre_topc(sK4,sK2)),
% 0.22/0.61    inference(subsumption_resolution,[],[f764,f51])).
% 0.22/0.61  fof(f764,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2)),
% 0.22/0.61    inference(resolution,[],[f761,f453])).
% 0.22/0.61  fof(f453,plain,(
% 0.22/0.61    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.61    inference(backward_demodulation,[],[f164,f447])).
% 0.22/0.61  fof(f447,plain,(
% 0.22/0.61    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_tmap_1(sK3,sK1,sK5,sK2)),
% 0.22/0.61    inference(forward_demodulation,[],[f444,f184])).
% 0.22/0.61  fof(f184,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2))),
% 0.22/0.61    inference(resolution,[],[f175,f53])).
% 0.22/0.61  fof(f444,plain,(
% 0.22/0.61    k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2))),
% 0.22/0.61    inference(resolution,[],[f250,f53])).
% 0.22/0.61  fof(f164,plain,(
% 0.22/0.61    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f163,f47])).
% 0.22/0.61  fof(f47,plain,(
% 0.22/0.61    ~v2_struct_0(sK2)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f163,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f162,f98])).
% 0.22/0.61  fof(f98,plain,(
% 0.22/0.61    v2_pre_topc(sK2)),
% 0.22/0.61    inference(resolution,[],[f96,f48])).
% 0.22/0.61  fof(f48,plain,(
% 0.22/0.61    m1_pre_topc(sK2,sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f162,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f161,f81])).
% 0.22/0.61  fof(f81,plain,(
% 0.22/0.61    l1_pre_topc(sK2)),
% 0.22/0.61    inference(resolution,[],[f79,f48])).
% 0.22/0.61  fof(f161,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f160,f44])).
% 0.22/0.61  fof(f160,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f159,f45])).
% 0.22/0.61  fof(f159,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f158,f46])).
% 0.22/0.61  fof(f158,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f157,f58])).
% 0.22/0.61  fof(f58,plain,(
% 0.22/0.61    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f157,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f156,f59])).
% 0.22/0.61  fof(f59,plain,(
% 0.22/0.61    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f156,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f155,f61])).
% 0.22/0.61  fof(f61,plain,(
% 0.22/0.61    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f155,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v1_funct_1(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(resolution,[],[f70,f60])).
% 0.22/0.61  fof(f60,plain,(
% 0.22/0.61    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f39])).
% 0.22/0.61  fof(f70,plain,(
% 0.22/0.61    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f28])).
% 0.22/0.61  fof(f28,plain,(
% 0.22/0.61    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f27])).
% 0.22/0.61  fof(f27,plain,(
% 0.22/0.61    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f7])).
% 0.22/0.61  fof(f7,axiom,(
% 0.22/0.61    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).
% 0.22/0.61  fof(f761,plain,(
% 0.22/0.61    ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)),
% 0.22/0.61    inference(subsumption_resolution,[],[f725,f757])).
% 0.22/0.61  fof(f757,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f756,f41])).
% 0.22/0.61  fof(f756,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f755,f42])).
% 0.22/0.61  fof(f755,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f754,f43])).
% 0.22/0.61  fof(f754,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f753,f44])).
% 0.22/0.61  fof(f753,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f752,f45])).
% 0.22/0.61  fof(f752,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f751,f46])).
% 0.22/0.61  fof(f751,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f750,f48])).
% 0.22/0.61  fof(f750,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f749,f52])).
% 0.22/0.61  fof(f749,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f748,f286])).
% 0.22/0.61  fof(f286,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))),
% 0.22/0.61    inference(subsumption_resolution,[],[f285,f82])).
% 0.22/0.61  fof(f285,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(sK3)),
% 0.22/0.61    inference(resolution,[],[f264,f63])).
% 0.22/0.61  fof(f264,plain,(
% 0.22/0.61    ~m1_pre_topc(sK3,sK3) | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2))),
% 0.22/0.61    inference(subsumption_resolution,[],[f263,f49])).
% 0.22/0.61  fof(f263,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f262,f99])).
% 0.22/0.61  fof(f262,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f261,f82])).
% 0.22/0.61  fof(f261,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f258,f53])).
% 0.22/0.61  fof(f258,plain,(
% 0.22/0.61    v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(superposition,[],[f153,f254])).
% 0.22/0.61  fof(f254,plain,(
% 0.22/0.61    k2_tmap_1(sK3,sK1,sK5,sK2) = k3_tmap_1(sK3,sK1,sK3,sK2,sK5)),
% 0.22/0.61    inference(forward_demodulation,[],[f251,f184])).
% 0.22/0.61  fof(f251,plain,(
% 0.22/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK5)),
% 0.22/0.61    inference(resolution,[],[f247,f53])).
% 0.22/0.61  fof(f748,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f747,f449])).
% 0.22/0.61  fof(f449,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.61    inference(backward_demodulation,[],[f59,f447])).
% 0.22/0.61  fof(f747,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f746,f373])).
% 0.22/0.61  fof(f373,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.61    inference(subsumption_resolution,[],[f372,f82])).
% 0.22/0.61  fof(f372,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK3)),
% 0.22/0.61    inference(resolution,[],[f274,f63])).
% 0.22/0.61  fof(f274,plain,(
% 0.22/0.61    ~m1_pre_topc(sK3,sK3) | m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.61    inference(subsumption_resolution,[],[f273,f49])).
% 0.22/0.61  fof(f273,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f272,f99])).
% 0.22/0.61  fof(f272,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f271,f82])).
% 0.22/0.61  fof(f271,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f270,f44])).
% 0.22/0.61  fof(f270,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f269,f45])).
% 0.22/0.61  fof(f269,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f268,f46])).
% 0.22/0.61  fof(f268,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f267,f53])).
% 0.22/0.61  fof(f267,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f266,f55])).
% 0.22/0.61  fof(f266,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f265,f56])).
% 0.22/0.61  fof(f265,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(subsumption_resolution,[],[f259,f57])).
% 0.22/0.61  fof(f259,plain,(
% 0.22/0.61    m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.22/0.61    inference(superposition,[],[f77,f254])).
% 0.22/0.61  fof(f746,plain,(
% 0.22/0.61    v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(superposition,[],[f76,f686])).
% 0.22/0.61  fof(f686,plain,(
% 0.22/0.61    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))),
% 0.22/0.61    inference(subsumption_resolution,[],[f685,f41])).
% 0.22/0.61  fof(f685,plain,(
% 0.22/0.61    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f684,f42])).
% 0.22/0.61  fof(f684,plain,(
% 0.22/0.61    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f678,f43])).
% 0.22/0.61  fof(f678,plain,(
% 0.22/0.61    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(resolution,[],[f674,f48])).
% 0.22/0.61  fof(f674,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_pre_topc(sK2,X0) | k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(forward_demodulation,[],[f672,f459])).
% 0.22/0.61  fof(f459,plain,(
% 0.22/0.61    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4))),
% 0.22/0.61    inference(backward_demodulation,[],[f214,f447])).
% 0.22/0.61  fof(f214,plain,(
% 0.22/0.61    k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4))),
% 0.22/0.61    inference(resolution,[],[f183,f54])).
% 0.22/0.61  fof(f183,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1))) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f182,f47])).
% 0.22/0.61  fof(f182,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f181,f98])).
% 0.22/0.61  fof(f181,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f180,f81])).
% 0.22/0.61  fof(f180,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f179,f44])).
% 0.22/0.61  fof(f179,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f178,f45])).
% 0.22/0.61  fof(f178,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f177,f46])).
% 0.22/0.61  fof(f177,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f176,f58])).
% 0.22/0.61  fof(f176,plain,(
% 0.22/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f167,f59])).
% 0.22/0.62  fof(f167,plain,(
% 0.22/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X1) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(resolution,[],[f67,f61])).
% 0.22/0.62  fof(f672,plain,(
% 0.22/0.62    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK4)) = k3_tmap_1(X0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.62    inference(resolution,[],[f464,f54])).
% 0.22/0.62  fof(f464,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f388,f449])).
% 0.22/0.62  fof(f388,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f387,f69])).
% 0.22/0.62  fof(f387,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f386,f44])).
% 0.22/0.62  fof(f386,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK2,X4) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f385,f45])).
% 0.22/0.62  fof(f385,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK2,X4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f384,f46])).
% 0.22/0.62  fof(f384,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK2,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f375,f286])).
% 0.22/0.62  fof(f375,plain,(
% 0.22/0.62    ( ! [X4,X3] : (~m1_pre_topc(X3,sK2) | k3_tmap_1(X4,sK1,sK2,X3,k2_tmap_1(sK3,sK1,sK5,sK2)) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(X3)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK2,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.22/0.62    inference(resolution,[],[f373,f65])).
% 0.22/0.62  fof(f725,plain,(
% 0.22/0.62    ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 0.22/0.62    inference(subsumption_resolution,[],[f691,f724])).
% 0.22/0.62  fof(f724,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.62    inference(subsumption_resolution,[],[f723,f81])).
% 0.22/0.62  fof(f723,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_pre_topc(sK2)),
% 0.22/0.62    inference(resolution,[],[f712,f63])).
% 0.22/0.62  fof(f712,plain,(
% 0.22/0.62    ~m1_pre_topc(sK2,sK2) | m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 0.22/0.62    inference(subsumption_resolution,[],[f711,f47])).
% 0.22/0.62  fof(f711,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f710,f98])).
% 0.22/0.62  fof(f710,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f709,f81])).
% 0.22/0.62  fof(f709,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f708,f44])).
% 0.22/0.62  fof(f708,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f707,f45])).
% 0.22/0.62  fof(f707,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f706,f46])).
% 0.22/0.62  fof(f706,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f705,f54])).
% 0.22/0.62  fof(f705,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f704,f286])).
% 0.22/0.62  fof(f704,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f703,f449])).
% 0.22/0.62  fof(f703,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f701,f373])).
% 0.22/0.62  fof(f701,plain,(
% 0.22/0.62    m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(superposition,[],[f77,f683])).
% 0.22/0.62  fof(f683,plain,(
% 0.22/0.62    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2))),
% 0.22/0.62    inference(subsumption_resolution,[],[f682,f47])).
% 0.22/0.62  fof(f682,plain,(
% 0.22/0.62    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f681,f98])).
% 0.22/0.62  fof(f681,plain,(
% 0.22/0.62    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(subsumption_resolution,[],[f680,f81])).
% 0.22/0.62  fof(f680,plain,(
% 0.22/0.62    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.22/0.62    inference(duplicate_literal_removal,[],[f677])).
% 0.22/0.62  fof(f677,plain,(
% 0.22/0.62    k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) = k3_tmap_1(sK2,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.62    inference(resolution,[],[f674,f63])).
% 0.22/0.62  fof(f691,plain,(
% 0.22/0.62    ~v1_funct_2(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4))),
% 0.22/0.62    inference(forward_demodulation,[],[f690,f686])).
% 0.22/0.62  fof(f690,plain,(
% 0.22/0.62    ~m1_subset_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.62    inference(forward_demodulation,[],[f689,f686])).
% 0.22/0.62  fof(f689,plain,(
% 0.22/0.62    k2_tmap_1(sK3,sK1,sK5,sK4) = k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4) | ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.62    inference(forward_demodulation,[],[f687,f686])).
% 0.22/0.62  fof(f687,plain,(
% 0.22/0.62    ~v1_funct_1(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),sK4)) | k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 0.22/0.62    inference(backward_demodulation,[],[f637,f686])).
% 0.22/0.62  fof(f637,plain,(
% 0.22/0.62    k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)))),
% 0.22/0.62    inference(subsumption_resolution,[],[f636,f346])).
% 0.22/0.62  fof(f636,plain,(
% 0.22/0.62    k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)))),
% 0.22/0.62    inference(subsumption_resolution,[],[f635,f520])).
% 0.22/0.62  fof(f635,plain,(
% 0.22/0.62    k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)))),
% 0.22/0.62    inference(subsumption_resolution,[],[f634,f421])).
% 0.22/0.62  fof(f634,plain,(
% 0.22/0.62    k2_tmap_1(sK3,sK1,sK5,sK4) = k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,sK5,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)))),
% 0.22/0.62    inference(resolution,[],[f630,f73])).
% 0.22/0.62  fof(f73,plain,(
% 0.22/0.62    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f40])).
% 0.22/0.62  fof(f40,plain,(
% 0.22/0.62    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.62    inference(nnf_transformation,[],[f30])).
% 0.22/0.62  fof(f30,plain,(
% 0.22/0.62    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.62    inference(flattening,[],[f29])).
% 0.22/0.62  fof(f29,plain,(
% 0.22/0.62    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.62    inference(ennf_transformation,[],[f1])).
% 0.22/0.62  fof(f1,axiom,(
% 0.22/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.62  fof(f630,plain,(
% 0.22/0.62    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k2_tmap_1(sK3,sK1,sK5,sK4))),
% 0.22/0.62    inference(forward_demodulation,[],[f629,f474])).
% 0.22/0.62  fof(f629,plain,(
% 0.22/0.62    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 0.22/0.62    inference(subsumption_resolution,[],[f627,f51])).
% 0.22/0.62  fof(f627,plain,(
% 0.22/0.62    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k2_tmap_1(sK3,sK1,sK5,sK2)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) | v2_struct_0(sK4)),
% 0.22/0.62    inference(resolution,[],[f606,f54])).
% 0.22/0.62  fof(f606,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0,k2_tmap_1(sK3,sK1,sK5,sK2)),k3_tmap_1(sK0,sK1,sK3,X0,sK5)) | v2_struct_0(X0)) )),
% 0.22/0.62    inference(forward_demodulation,[],[f605,f447])).
% 0.22/0.62  fof(f605,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,X0,sK5))) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f602,f47])).
% 0.22/0.62  fof(f602,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v2_struct_0(sK2) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,X0,sK5))) )),
% 0.22/0.62    inference(resolution,[],[f538,f53])).
% 0.22/0.62  fof(f538,plain,(
% 0.22/0.62    ( ! [X2,X3] : (~m1_pre_topc(X3,sK3) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | v2_struct_0(X3) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5))) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f537,f41])).
% 0.22/0.62  fof(f537,plain,(
% 0.22/0.62    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X2) | v2_struct_0(X3) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5)) | v2_struct_0(sK0)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f536,f42])).
% 0.22/0.62  fof(f536,plain,(
% 0.22/0.62    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X2) | v2_struct_0(X3) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f531,f43])).
% 0.22/0.62  fof(f531,plain,(
% 0.22/0.62    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X2) | v2_struct_0(X3) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k3_tmap_1(sK0,sK1,sK3,X2,sK5)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.62    inference(resolution,[],[f359,f50])).
% 0.22/0.62  fof(f359,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X0) | v2_struct_0(X2) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f358,f69])).
% 0.22/0.62  fof(f358,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f357,f69])).
% 0.22/0.62  fof(f357,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f356,f44])).
% 0.22/0.62  fof(f356,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f355,f45])).
% 0.22/0.62  fof(f355,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f354,f46])).
% 0.22/0.62  fof(f354,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f353,f49])).
% 0.22/0.62  fof(f353,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f352,f55])).
% 0.22/0.62  fof(f352,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f348,f56])).
% 0.22/0.62  fof(f348,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK3,X2,sK5)),k3_tmap_1(X1,sK1,sK3,X0,sK5)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(resolution,[],[f66,f57])).
% 0.22/0.62  fof(f66,plain,(
% 0.22/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f20])).
% 0.22/0.62  fof(f20,plain,(
% 0.22/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.62    inference(flattening,[],[f19])).
% 0.22/0.62  fof(f19,plain,(
% 0.22/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.62    inference(ennf_transformation,[],[f9])).
% 0.22/0.62  fof(f9,axiom,(
% 0.22/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 0.22/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).
% 0.22/0.62  fof(f456,plain,(
% 0.22/0.62    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK5,sK2),X0),X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.62    inference(backward_demodulation,[],[f197,f447])).
% 0.22/0.62  fof(f197,plain,(
% 0.22/0.62    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f196,f47])).
% 0.22/0.62  fof(f196,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f195,f98])).
% 0.22/0.62  fof(f195,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f194,f81])).
% 0.22/0.62  fof(f194,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f193,f44])).
% 0.22/0.62  fof(f193,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f192,f45])).
% 0.22/0.62  fof(f192,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f191,f46])).
% 0.22/0.62  fof(f191,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f190,f58])).
% 0.22/0.62  fof(f190,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f189,f59])).
% 0.22/0.62  fof(f189,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f188,f61])).
% 0.22/0.62  fof(f188,plain,(
% 0.22/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0),X0,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.62    inference(resolution,[],[f72,f60])).
% 0.22/0.62  fof(f72,plain,(
% 0.22/0.62    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f28])).
% 0.22/0.62  % SZS output end Proof for theBenchmark
% 0.22/0.62  % (11470)------------------------------
% 0.22/0.62  % (11470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.62  % (11470)Termination reason: Refutation
% 0.22/0.62  
% 0.22/0.62  % (11470)Memory used [KB]: 7036
% 0.22/0.62  % (11470)Time elapsed: 0.188 s
% 0.22/0.62  % (11470)------------------------------
% 0.22/0.62  % (11470)------------------------------
% 0.22/0.62  % (11466)Success in time 0.254 s
%------------------------------------------------------------------------------

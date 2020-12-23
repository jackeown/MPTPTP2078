%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 (1395 expanded)
%              Number of leaves         :   11 ( 730 expanded)
%              Depth                    :  120
%              Number of atoms          : 2417 (39182 expanded)
%              Number of equality atoms :   14 (1348 expanded)
%              Maximal formula depth    :   34 (  14 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(resolution,[],[f201,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r4_tsep_1(sK0,sK2,sK3)
    & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & sK0 = k1_tsep_1(sK0,sK2,sK3)
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
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK0 = k1_tsep_1(sK0,X2,X3)
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
                        ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1)
                          | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                        & r4_tsep_1(sK0,X2,X3)
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK0 = k1_tsep_1(sK0,X2,X3)
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
                      ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1)
                        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                      & r4_tsep_1(sK0,X2,X3)
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(X5,X3,sK1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & sK0 = k1_tsep_1(sK0,X2,X3)
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
                    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1)
                      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                    & r4_tsep_1(sK0,X2,X3)
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(X5,X3,sK1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & sK0 = k1_tsep_1(sK0,X2,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1)
                    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                  & r4_tsep_1(sK0,sK2,X3)
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(X5,X3,sK1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & sK0 = k1_tsep_1(sK0,sK2,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1)
                  | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                  | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                & r4_tsep_1(sK0,sK2,X3)
                & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(X5,X3,sK1)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & sK0 = k1_tsep_1(sK0,sK2,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1)
                | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
              & r4_tsep_1(sK0,sK2,sK3)
              & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(X5,sK3,sK1)
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & sK0 = k1_tsep_1(sK0,sK2,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1)
              | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
              | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
            & r4_tsep_1(sK0,sK2,sK3)
            & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5)
            & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(X5,sK3,sK1)
            & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(X4,sK2,sK1)
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1)
            | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
          & r4_tsep_1(sK0,sK2,sK3)
          & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5)
          & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(X5,sK3,sK1)
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
        & r4_tsep_1(sK0,sK2,sK3)
        & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5)
        & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(X5,sK3,sK1)
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
      & r4_tsep_1(sK0,sK2,sK3)
      & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
      & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v5_pre_topc(sK5,sK3,sK1)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
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
                             => ( ( r4_tsep_1(X0,X2,X3)
                                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
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
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_tmap_1)).

fof(f201,plain,(
    v2_struct_0(sK0) ),
    inference(resolution,[],[f200,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f200,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f199,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f199,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f198,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f198,plain,
    ( v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f197,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f196,f30])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f196,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f195,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f195,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f194,f31])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f194,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f193,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f193,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f192,f35])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f192,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f191,f37])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f191,plain,
    ( ~ v1_funct_1(sK4)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f190,f41])).

fof(f41,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f190,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f189,f38])).

fof(f38,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f189,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f187,f42])).

fof(f42,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f187,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f186,f40])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f186,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f184,f44])).

fof(f44,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f184,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f181,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(cnf_transformation,[],[f16])).

% (29522)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (29524)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f181,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f180,f27])).

fof(f180,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f179,f30])).

fof(f179,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f178,f28])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f177,f31])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f176,f33])).

fof(f176,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f175,f35])).

fof(f175,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f174,f37])).

fof(f174,plain,
    ( ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f173,f41])).

fof(f173,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f172,f38])).

fof(f172,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f171,f42])).

fof(f171,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f170,f40])).

fof(f170,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f169,f44])).

fof(f169,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f167,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f61,f36])).

fof(f36,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f16])).

fof(f167,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f166,f38])).

fof(f166,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f165,f42])).

fof(f165,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f164,f40])).

fof(f164,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f163,f44])).

fof(f163,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f62,f36])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f16])).

fof(f161,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f160,f44])).

fof(f160,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f159,f43])).

fof(f43,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f159,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f158,f48])).

fof(f48,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f158,plain,(
    ! [X0] :
      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f157,f30])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f156,f31])).

fof(f156,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f155,f37])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f154,f38])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_1(sK4)
      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f153,f39])).

fof(f39,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK4,sK2,sK1)
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK3,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(sK4,sK2,sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f151,f40])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0)
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f150,f27])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f149,f28])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK2)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f148,f33])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f147,f35])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f146,f36])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),k1_tsep_1(sK0,sK2,sK3),X1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f145])).

% (29528)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f145,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK3,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,sK2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),k1_tsep_1(sK0,sK2,sK3),X1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f142,f47])).

fof(f47,plain,(
    r4_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f142,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r4_tsep_1(X8,sK2,sK3)
      | v2_struct_0(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X10))))
      | ~ v5_pre_topc(X9,sK3,X10)
      | ~ v1_funct_2(X9,u1_struct_0(sK3),u1_struct_0(X10))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X10))))
      | ~ v5_pre_topc(X11,sK2,X10)
      | ~ v1_funct_2(X11,u1_struct_0(sK2),u1_struct_0(X10))
      | ~ v1_funct_1(X11)
      | v5_pre_topc(k10_tmap_1(X8,X10,sK2,sK3,X11,X9),k1_tsep_1(X8,sK2,sK3),X10)
      | ~ m1_pre_topc(sK3,X8)
      | ~ m1_pre_topc(sK2,X8)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X10,X8,X11,X9] :
      ( v2_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | ~ r4_tsep_1(X8,sK2,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X10))))
      | ~ v5_pre_topc(X9,sK3,X10)
      | ~ v1_funct_2(X9,u1_struct_0(sK3),u1_struct_0(X10))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X10))))
      | ~ v5_pre_topc(X11,sK2,X10)
      | ~ v1_funct_2(X11,u1_struct_0(sK2),u1_struct_0(X10))
      | ~ v1_funct_1(X11)
      | v5_pre_topc(k10_tmap_1(X8,X10,sK2,sK3,X11,X9),k1_tsep_1(X8,sK2,sK3),X10)
      | ~ m1_pre_topc(sK3,X8)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,X8)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
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
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
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
                 => ( r1_tsep_1(X2,X3)
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
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

fof(f138,plain,
    ( r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f137,f27])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f136,f30])).

fof(f136,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f135,f28])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f134,f31])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f133,f33])).

fof(f133,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f132,f35])).

fof(f132,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f131,f37])).

fof(f131,plain,
    ( ~ v1_funct_1(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f130,f41])).

fof(f130,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f129,f38])).

fof(f129,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f128,f42])).

fof(f128,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f127,f40])).

fof(f127,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f125,f44])).

fof(f125,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f122,f60])).

fof(f122,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f121,f27])).

fof(f121,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f120,f30])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f119,f28])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f118,f31])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f117,f33])).

fof(f117,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f116,f35])).

fof(f116,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f115,f37])).

fof(f115,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(resolution,[],[f114,f41])).

fof(f114,plain,
    ( ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(resolution,[],[f113,f38])).

fof(f113,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(resolution,[],[f112,f42])).

fof(f112,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f111,f40])).

fof(f111,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f110,f44])).

fof(f110,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f108,f65])).

fof(f108,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f107,f38])).

fof(f107,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f106,f42])).

fof(f106,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f105,f40])).

fof(f105,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f104,f44])).

fof(f104,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f66])).

fof(f102,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f101,f40])).

fof(f101,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK0)
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f100,f44])).

fof(f100,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f99,f39])).

fof(f99,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f98,f43])).

fof(f98,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f94,f47])).

fof(f94,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f91,f36])).

fof(f91,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

fof(f81,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f80,f41])).

fof(f80,plain,
    ( ~ v1_funct_1(sK5)
    | v2_struct_0(sK2)
    | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f42])).

fof(f79,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK5)
    | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f44])).

% (29520)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f78,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f77,f64])).

fof(f64,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(backward_demodulation,[],[f46,f36])).

fof(f46,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | v2_struct_0(sK3)
    | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f76,f63])).

fof(f63,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(backward_demodulation,[],[f45,f36])).

fof(f45,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | r1_tsep_1(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f75,f30])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f74,f31])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f37])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f38])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK4)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f71,f40])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK2,k2_tsep_1(sK0,sK2,sK3),X2),k3_tmap_1(sK0,X1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f70,f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK2,k2_tsep_1(sK0,sK2,sK3),X2),k3_tmap_1(sK0,X1,sK3,k2_tsep_1(sK0,sK2,sK3),X0))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f69,f28])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK2,k2_tsep_1(sK0,sK2,sK3),X1),k3_tmap_1(sK0,X0,sK3,k2_tsep_1(sK0,sK2,sK3),X2))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK2,sK0)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
      | v2_struct_0(sK3)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK2,k2_tsep_1(sK0,sK2,sK3),X1),k3_tmap_1(sK0,X0,sK3,k2_tsep_1(sK0,sK2,sK3),X2))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f67,f35])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK3,sK0)
      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK2,k2_tsep_1(sK0,sK2,sK3),X1),k3_tmap_1(sK0,X0,sK3,k2_tsep_1(sK0,sK2,sK3),X2))
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | r1_tsep_1(sK2,sK3)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f53,f36])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (29541)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.46  % (29530)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.46  % (29529)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.47  % (29530)Refutation not found, incomplete strategy% (29530)------------------------------
% 0.21/0.47  % (29530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29530)Memory used [KB]: 10746
% 0.21/0.47  % (29530)Time elapsed: 0.056 s
% 0.21/0.47  % (29530)------------------------------
% 0.21/0.47  % (29530)------------------------------
% 0.21/0.48  % (29529)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(resolution,[],[f201,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ((((((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f22,f21,f20,f19,f18,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5))) & r4_tsep_1(sK0,sK2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5))) & r4_tsep_1(sK0,sK2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_tmap_1)).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f200,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f199,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f198,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~v2_struct_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f197,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(sK3) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f196,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v2_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f195,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK3) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f194,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f193,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f192,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f191,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f190,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v1_funct_1(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ~v1_funct_1(sK5) | v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK1) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f189,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0) | v2_struct_0(sK3) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | v2_struct_0(sK1) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f187,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(sK3) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f186,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK3) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f184,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f181,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % (29522)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (29524)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f180,f27])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f179,f30])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f178,f28])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f177,f31])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f176,f33])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f175,f35])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f174,f37])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f173,f41])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f172,f38])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f171,f42])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.49    inference(resolution,[],[f170,f40])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.49    inference(resolution,[],[f169,f44])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK3) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v2_struct_0(sK3) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f167,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f61,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | v2_struct_0(sK3) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f166,f38])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f165,f42])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f164,f40])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f163,f44])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f161,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f62,f36])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f160,f44])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f159,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v5_pre_topc(sK5,sK3,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f158,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X0] : (v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v1_funct_1(X0) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f157,f30])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | v2_struct_0(sK1) | ~v1_funct_1(X0) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f156,f31])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | v2_struct_0(sK1) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f155,f37])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f154,f38])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_1(sK4) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f153,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v5_pre_topc(sK4,sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_pre_topc(sK4,sK2,sK1) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK3,sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK0,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f151,f40])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK0) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f150,f27])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK2) | v2_struct_0(sK3)) )),
% 0.21/0.49    inference(resolution,[],[f149,f28])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK2) | ~v2_pre_topc(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f148,f33])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f147,f35])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(sK3,sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),sK0,X1) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f146,f36])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),k1_tsep_1(sK0,sK2,sK3),X1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.49  % (29528)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK3,X1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | v5_pre_topc(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),k1_tsep_1(sK0,sK2,sK3),X1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f142,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    r4_tsep_1(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X10,X8,X11,X9] : (~r4_tsep_1(X8,sK2,sK3) | v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X10)))) | ~v5_pre_topc(X9,sK3,X10) | ~v1_funct_2(X9,u1_struct_0(sK3),u1_struct_0(X10)) | ~v1_funct_1(X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X10)))) | ~v5_pre_topc(X11,sK2,X10) | ~v1_funct_2(X11,u1_struct_0(sK2),u1_struct_0(X10)) | ~v1_funct_1(X11) | v5_pre_topc(k10_tmap_1(X8,X10,sK2,sK3,X11,X9),k1_tsep_1(X8,sK2,sK3),X10) | ~m1_pre_topc(sK3,X8) | ~m1_pre_topc(sK2,X8) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X10,X8,X11,X9] : (v2_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~r4_tsep_1(X8,sK2,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X10)))) | ~v5_pre_topc(X9,sK3,X10) | ~v1_funct_2(X9,u1_struct_0(sK3),u1_struct_0(X10)) | ~v1_funct_1(X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X10)))) | ~v5_pre_topc(X11,sK2,X10) | ~v1_funct_2(X11,u1_struct_0(sK2),u1_struct_0(X10)) | ~v1_funct_1(X11) | v5_pre_topc(k10_tmap_1(X8,X10,sK2,sK3,X11,X9),k1_tsep_1(X8,sK2,sK3),X10) | ~m1_pre_topc(sK3,X8) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X8) | v2_struct_0(sK2) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 0.21/0.49    inference(resolution,[],[f138,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tsep_1(X2,X3) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    r1_tsep_1(sK2,sK3) | v2_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)),
% 0.21/0.49    inference(resolution,[],[f137,f27])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK1) | v2_struct_0(sK2) | v2_struct_0(sK3)),
% 0.21/0.49    inference(resolution,[],[f136,f30])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f135,f28])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK2) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f134,f31])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f133,f33])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f132,f35])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f131,f37])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | v2_struct_0(sK3) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f130,f41])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~v1_funct_1(sK5) | v2_struct_0(sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f129,f38])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK3) | ~v1_funct_1(sK5) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f128,f42])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK2) | v2_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK3) | ~v1_funct_1(sK5) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f127,f40])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK3) | v2_struct_0(sK2) | v2_struct_0(sK0) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f125,f44])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK2) | v2_struct_0(sK0) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f122,f60])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK2) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f121,f27])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK2) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f120,f30])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f119,f28])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v2_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f118,f31])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f117,f33])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f116,f35])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f115,f37])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(resolution,[],[f114,f41])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(resolution,[],[f113,f38])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(resolution,[],[f112,f42])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(sK4) | ~v1_funct_1(sK5) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.49    inference(resolution,[],[f111,f40])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.49    inference(resolution,[],[f110,f44])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    r1_tsep_1(sK2,sK3) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f108,f65])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f107,f38])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(sK5) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f106,f42])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f105,f40])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | v2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f104,f44])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    v2_struct_0(sK3) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f102,f66])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK3) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK2) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f101,f40])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v2_struct_0(sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f100,f44])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f99,f39])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~v5_pre_topc(sK4,sK2,sK1) | v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | r1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f98,f43])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~v5_pre_topc(sK5,sK3,sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.49    inference(resolution,[],[f97,f48])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f94,f47])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~r4_tsep_1(sK0,sK2,sK3) | v2_struct_0(sK2) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(forward_demodulation,[],[f91,f36])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    v2_struct_0(sK2) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v2_struct_0(sK2) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f81,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) | v2_struct_0(sK2) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f80,f41])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~v1_funct_1(sK5) | v2_struct_0(sK2) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f79,f42])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~v1_funct_1(sK5) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f78,f44])).
% 0.21/0.49  % (29520)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) | v2_struct_0(sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f77,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 0.21/0.49    inference(backward_demodulation,[],[f46,f36])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) | v2_struct_0(sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f76,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.21/0.49    inference(backward_demodulation,[],[f45,f36])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tsep_1(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f75,f30])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f74,f31])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f73,f37])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f72,f38])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X0)),sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f71,f40])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK2,k2_tsep_1(sK0,sK2,sK3),X2),k3_tmap_1(sK0,X1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f70,f27])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK2,k2_tsep_1(sK0,sK2,sK3),X2),k3_tmap_1(sK0,X1,sK3,k2_tsep_1(sK0,sK2,sK3),X0)) | v2_struct_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,sK0,sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f69,f28])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK2,k2_tsep_1(sK0,sK2,sK3),X1),k3_tmap_1(sK0,X0,sK3,k2_tsep_1(sK0,sK2,sK3),X2)) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f68,f33])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(sK2,sK0) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | v2_struct_0(sK3) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK2,k2_tsep_1(sK0,sK2,sK3),X1),k3_tmap_1(sK0,X0,sK3,k2_tsep_1(sK0,sK2,sK3),X2)) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f67,f35])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(sK3,sK0) | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK2,k2_tsep_1(sK0,sK2,sK3),X1),k3_tmap_1(sK0,X0,sK3,k2_tsep_1(sK0,sK2,sK3),X2)) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | r1_tsep_1(sK2,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f53,f36])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29529)------------------------------
% 0.21/0.49  % (29529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29529)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29529)Memory used [KB]: 2174
% 0.21/0.49  % (29529)Time elapsed: 0.067 s
% 0.21/0.49  % (29529)------------------------------
% 0.21/0.49  % (29529)------------------------------
% 0.21/0.49  % (29519)Success in time 0.136 s
%------------------------------------------------------------------------------

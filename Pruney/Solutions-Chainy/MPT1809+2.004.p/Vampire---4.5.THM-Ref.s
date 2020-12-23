%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  167 (3064 expanded)
%              Number of leaves         :   13 (1562 expanded)
%              Depth                    :   56
%              Number of atoms          : 1962 (74839 expanded)
%              Number of equality atoms :   95 (10925 expanded)
%              Maximal formula depth    :   31 (  13 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(subsumption_resolution,[],[f384,f252])).

fof(f252,plain,(
    ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f251,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
      | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
    & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
      | r1_tmap_1(sK0,sK1,sK2,sK5) )
    & sK5 = sK7
    & sK5 = sK6
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & sK0 = k1_tsep_1(sK0,sK3,sK4)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f27,f26,f25,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | r1_tmap_1(X0,X1,X2,X5) )
                                    & X5 = X7
                                    & X5 = X6
                                    & m1_subset_1(X7,u1_struct_0(X4)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(sK0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) )
                                    | r1_tmap_1(sK0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & sK0 = k1_tsep_1(sK0,X3,X4)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)
                                  | ~ r1_tmap_1(sK0,X1,X2,X5) )
                                & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                    & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) )
                                  | r1_tmap_1(sK0,X1,X2,X5) )
                                & X5 = X7
                                & X5 = X6
                                & m1_subset_1(X7,u1_struct_0(X4)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK0)) )
                    & sK0 = k1_tsep_1(sK0,X3,X4)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)
                                | ~ r1_tmap_1(sK0,sK1,X2,X5) )
                              & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                                  & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) )
                                | r1_tmap_1(sK0,sK1,X2,X5) )
                              & X5 = X7
                              & X5 = X6
                              & m1_subset_1(X7,u1_struct_0(X4)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(sK0)) )
                  & sK0 = k1_tsep_1(sK0,X3,X4)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)
                              | ~ r1_tmap_1(sK0,sK1,X2,X5) )
                            & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                                & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) )
                              | r1_tmap_1(sK0,sK1,X2,X5) )
                            & X5 = X7
                            & X5 = X6
                            & m1_subset_1(X7,u1_struct_0(X4)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(sK0)) )
                & sK0 = k1_tsep_1(sK0,X3,X4)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)
                            | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                          & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                              & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) )
                            | r1_tmap_1(sK0,sK1,sK2,X5) )
                          & X5 = X7
                          & X5 = X6
                          & m1_subset_1(X7,u1_struct_0(X4)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(sK0)) )
              & sK0 = k1_tsep_1(sK0,X3,X4)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)
                          | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                        & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                            & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) )
                          | r1_tmap_1(sK0,sK1,sK2,X5) )
                        & X5 = X7
                        & X5 = X6
                        & m1_subset_1(X7,u1_struct_0(X4)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,u1_struct_0(sK0)) )
            & sK0 = k1_tsep_1(sK0,X3,X4)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                        | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                      & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                          & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                        | r1_tmap_1(sK0,sK1,sK2,X5) )
                      & X5 = X7
                      & X5 = X6
                      & m1_subset_1(X7,u1_struct_0(X4)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,u1_struct_0(sK0)) )
          & sK0 = k1_tsep_1(sK0,sK3,X4)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                      | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                    & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                      | r1_tmap_1(sK0,sK1,sK2,X5) )
                    & X5 = X7
                    & X5 = X6
                    & m1_subset_1(X7,u1_struct_0(X4)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,u1_struct_0(sK0)) )
        & sK0 = k1_tsep_1(sK0,sK3,X4)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                    | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                  & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                      & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                    | r1_tmap_1(sK0,sK1,sK2,X5) )
                  & X5 = X7
                  & X5 = X6
                  & m1_subset_1(X7,u1_struct_0(sK4)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,u1_struct_0(sK0)) )
      & sK0 = k1_tsep_1(sK0,sK3,sK4)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                  | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                    & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                  | r1_tmap_1(sK0,sK1,sK2,X5) )
                & X5 = X7
                & X5 = X6
                & m1_subset_1(X7,u1_struct_0(sK4)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,u1_struct_0(sK0)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
              & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                  & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                | r1_tmap_1(sK0,sK1,sK2,sK5) )
              & sK5 = X7
              & sK5 = X6
              & m1_subset_1(X7,u1_struct_0(sK4)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
              | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
            & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
              | r1_tmap_1(sK0,sK1,sK2,sK5) )
            & sK5 = X7
            & sK5 = X6
            & m1_subset_1(X7,u1_struct_0(sK4)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
            | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
          & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
              & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
            | r1_tmap_1(sK0,sK1,sK2,sK5) )
          & sK5 = X7
          & sK5 = sK6
          & m1_subset_1(X7,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
          | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
        & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
            & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
          | r1_tmap_1(sK0,sK1,sK2,sK5) )
        & sK5 = X7
        & sK5 = sK6
        & m1_subset_1(X7,u1_struct_0(sK4)) )
   => ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
        | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
      & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
          & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
        | r1_tmap_1(sK0,sK1,sK2,sK5) )
      & sK5 = sK7
      & sK5 = sK6
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X4))
                                     => ( ( X5 = X7
                                          & X5 = X6 )
                                       => ( r1_tmap_1(X0,X1,X2,X5)
                                        <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( ( X5 = X7
                                        & X5 = X6 )
                                     => ( r1_tmap_1(X0,X1,X2,X5)
                                      <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

fof(f251,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f250,f35])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f250,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f249,f36])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f249,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f248,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f248,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f247,f38])).

fof(f38,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f247,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f246,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f246,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f245,f71])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f46,f48])).

fof(f48,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f245,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f244,f70])).

fof(f70,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f47,f49])).

fof(f49,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f244,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f243,f45])).

fof(f45,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f243,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f241,f185])).

fof(f185,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f184,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f183,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f182,f36])).

fof(f182,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f181,f37])).

fof(f181,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f180,f38])).

fof(f180,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f179,f39])).

fof(f179,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f178,f71])).

fof(f178,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f177,f70])).

fof(f177,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f176,f45])).

fof(f176,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f174,f68])).

fof(f68,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f67,f48])).

fof(f67,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f52,f49])).

fof(f52,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f174,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f173,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f172,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f80])).

fof(f80,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f79,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f77,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f76,f41])).

fof(f41,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f43,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f59,f44])).

fof(f44,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

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

fof(f170,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f43])).

fof(f162,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f154,f85])).

fof(f85,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f53,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f153,f31])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f32])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f33])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f40])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f41])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f63,f44])).

fof(f63,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X6 != X7
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                    & ( ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                    & ( ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                  <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                  <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
                                 => ( ( X6 = X7
                                      & X5 = X7 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                    <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_tmap_1)).

fof(f241,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f240,f31])).

fof(f240,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f239,f32])).

fof(f239,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f238,f33])).

fof(f238,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f80])).

fof(f237,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f41])).

fof(f229,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X10,X8,X9] :
      ( r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ r1_tmap_1(sK0,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f221,f85])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f220,f31])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f32])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f33])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f40])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f216,f41])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f42])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f206,f43])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ r1_tmap_1(sK0,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f65,f44])).

fof(f65,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X6 != X7
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f30])).

fof(f384,plain,(
    r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f383,f69])).

fof(f69,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f50,f48])).

fof(f50,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f383,plain,(
    ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f382,f34])).

fof(f382,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f381,f35])).

fof(f381,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f380,f36])).

fof(f380,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f379,f37])).

fof(f379,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f378,f38])).

fof(f378,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f377,f39])).

fof(f377,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f376,f71])).

fof(f376,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f375,f70])).

fof(f375,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f374,f45])).

fof(f374,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f373,f252])).

fof(f373,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f369,f66])).

fof(f66,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f51,f49])).

fof(f51,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f369,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f368,f31])).

fof(f368,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f367,f32])).

fof(f367,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f366,f33])).

fof(f366,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f365,f80])).

fof(f365,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f355,f41])).

fof(f355,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f349,f85])).

fof(f349,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f348,f31])).

fof(f348,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f347,f32])).

fof(f347,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f346,f33])).

fof(f346,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f345,f80])).

fof(f345,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f335,f43])).

fof(f335,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10)
      | r1_tmap_1(sK0,X8,X9,X10)
      | ~ r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK4))
      | ~ m1_subset_1(X10,u1_struct_0(sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f325,f85])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f324,f31])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f323,f32])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f322,f33])).

fof(f322,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f321,f40])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f320,f41])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f319,f42])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f308,f43])).

fof(f308,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2)
      | r1_tmap_1(sK0,X0,X1,X2)
      | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f61,f44])).

fof(f61,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | X6 != X7
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (15935)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.45  % (15935)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f386,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f384,f252])).
% 0.20/0.45  fof(f252,plain,(
% 0.20/0.45    ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f251,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ~v2_struct_0(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f27,f26,f25,f24,f23,f22,f21,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.20/0.46  fof(f251,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f250,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    v2_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f250,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f249,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    l1_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f249,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f248,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    v1_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f248,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f247,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f247,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f246,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f246,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f245,f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.46    inference(forward_demodulation,[],[f46,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    sK5 = sK6),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f245,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f244,f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.46    inference(forward_demodulation,[],[f47,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    sK5 = sK7),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f244,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f243,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f243,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f242])).
% 0.20/0.46  fof(f242,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(resolution,[],[f241,f185])).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f184,f34])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f183,f35])).
% 0.20/0.46  fof(f183,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f182,f36])).
% 0.20/0.46  fof(f182,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f181,f37])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f180,f38])).
% 0.20/0.46  fof(f180,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f179,f39])).
% 0.20/0.46  fof(f179,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f178,f71])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f177,f70])).
% 0.20/0.46  fof(f177,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f176,f45])).
% 0.20/0.46  fof(f176,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f175])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(resolution,[],[f174,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(backward_demodulation,[],[f67,f48])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(backward_demodulation,[],[f52,f49])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f173,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f172,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    v2_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f171,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f170,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f79,f31])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f78,f33])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f77,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ~v2_struct_0(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f76,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    m1_pre_topc(sK3,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f75,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ~v2_struct_0(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f74,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    m1_pre_topc(sK4,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(superposition,[],[f59,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f162,f43])).
% 0.20/0.46  fof(f162,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f161])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK4,sK0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f154,f85])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X6,X10,X8,X7,X9] : (k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(X6,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X6,X10,X8,X7,X9] : (k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(X9,X10) | ~m1_pre_topc(X6,X10) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | v2_struct_0(X10) | ~m1_pre_topc(X9,X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.46    inference(superposition,[],[f53,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f153,f31])).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f152,f32])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f151,f33])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f150,f40])).
% 0.20/0.46  fof(f150,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f149,f41])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f148,f42])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f139,f43])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f63,f44])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) & ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | (~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) & ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | (X6 != X7 | X5 != X7)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) => ((X6 = X7 & X5 = X7) => (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))))))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_tmap_1)).
% 0.20/0.46  fof(f241,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f240,f31])).
% 0.20/0.46  fof(f240,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f239,f32])).
% 0.20/0.46  fof(f239,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f238,f33])).
% 0.20/0.46  fof(f238,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f237,f80])).
% 0.20/0.46  fof(f237,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f229,f41])).
% 0.20/0.46  fof(f229,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f228])).
% 0.20/0.46  fof(f228,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~r1_tmap_1(sK0,X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK3,sK0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f221,f85])).
% 0.20/0.46  fof(f221,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f220,f31])).
% 0.20/0.46  fof(f220,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f219,f32])).
% 0.20/0.46  fof(f219,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f218,f33])).
% 0.20/0.46  fof(f218,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f217,f40])).
% 0.20/0.46  fof(f217,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f216,f41])).
% 0.20/0.46  fof(f216,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f215,f42])).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f206,f43])).
% 0.20/0.46  fof(f206,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~r1_tmap_1(sK0,X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f65,f44])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f384,plain,(
% 0.20/0.46    r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(resolution,[],[f383,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(backward_demodulation,[],[f50,f48])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f383,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f382,f34])).
% 0.20/0.46  fof(f382,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f381,f35])).
% 0.20/0.46  fof(f381,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f380,f36])).
% 0.20/0.46  fof(f380,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f379,f37])).
% 0.20/0.46  fof(f379,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f378,f38])).
% 0.20/0.46  fof(f378,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f377,f39])).
% 0.20/0.46  fof(f377,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f376,f71])).
% 0.20/0.46  fof(f376,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f375,f70])).
% 0.20/0.46  fof(f375,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f374,f45])).
% 0.20/0.46  fof(f374,plain,(
% 0.20/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f373,f252])).
% 0.20/0.46  fof(f373,plain,(
% 0.20/0.46    r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f370])).
% 0.20/0.46  fof(f370,plain,(
% 0.20/0.46    r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(resolution,[],[f369,f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(backward_demodulation,[],[f51,f49])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f369,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f368,f31])).
% 0.20/0.46  fof(f368,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f367,f32])).
% 0.20/0.46  fof(f367,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f366,f33])).
% 0.20/0.46  fof(f366,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f365,f80])).
% 0.20/0.46  fof(f365,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f355,f41])).
% 0.20/0.46  fof(f355,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f354])).
% 0.20/0.46  fof(f354,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k2_tmap_1(sK0,X8,X9,sK3),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK3,sK0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f349,f85])).
% 0.20/0.46  fof(f349,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f348,f31])).
% 0.20/0.46  fof(f348,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f347,f32])).
% 0.20/0.46  fof(f347,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f346,f33])).
% 0.20/0.46  fof(f346,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f345,f80])).
% 0.20/0.46  fof(f345,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f335,f43])).
% 0.20/0.46  fof(f335,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f334])).
% 0.20/0.46  fof(f334,plain,(
% 0.20/0.46    ( ! [X10,X8,X9] : (~r1_tmap_1(sK4,X8,k2_tmap_1(sK0,X8,X9,sK4),X10) | r1_tmap_1(sK0,X8,X9,X10) | ~r1_tmap_1(sK3,X8,k3_tmap_1(sK0,X8,sK0,sK3,X9),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK4)) | ~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK4,sK0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~v1_funct_1(X9) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f325,f85])).
% 0.20/0.46  fof(f325,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f324,f31])).
% 0.20/0.46  fof(f324,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f323,f32])).
% 0.20/0.46  fof(f323,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f322,f33])).
% 0.20/0.46  fof(f322,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f321,f40])).
% 0.20/0.46  fof(f321,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f320,f41])).
% 0.20/0.46  fof(f320,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f319,f42])).
% 0.20/0.46  fof(f319,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f308,f43])).
% 0.20/0.46  fof(f308,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,X1),X2) | r1_tmap_1(sK0,X0,X1,X2) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(superposition,[],[f61,f44])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15935)------------------------------
% 0.20/0.46  % (15935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15935)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15935)Memory used [KB]: 2046
% 0.20/0.46  % (15935)Time elapsed: 0.033 s
% 0.20/0.46  % (15935)------------------------------
% 0.20/0.46  % (15935)------------------------------
% 0.20/0.46  % (15914)Success in time 0.104 s
%------------------------------------------------------------------------------

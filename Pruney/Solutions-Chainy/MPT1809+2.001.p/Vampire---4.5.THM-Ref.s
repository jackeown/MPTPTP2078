%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  179 (1694 expanded)
%              Number of leaves         :   17 ( 862 expanded)
%              Depth                    :   54
%              Number of atoms          : 1706 (40773 expanded)
%              Number of equality atoms :   99 (6004 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f390,plain,(
    $false ),
    inference(subsumption_resolution,[],[f389,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f40,f39,f38,f37,f36,f35,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f389,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f388,f96])).

fof(f96,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f76,f53])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f388,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f387,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f387,plain,(
    ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f386,f284])).

fof(f284,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f283,f93])).

fof(f283,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f281,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f281,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f280,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f280,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f279,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f279,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f278,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f278,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f277,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f276,f49])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f276,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f275,f50])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f275,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f274,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f274,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f273,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f273,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f272,f53])).

fof(f272,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f271,f104])).

fof(f104,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f103,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f102,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f98,f57])).

fof(f57,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f78,f58])).

fof(f58,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
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

fof(f271,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f266,f108])).

fof(f108,plain,(
    ! [X6,X4,X7,X5] :
      ( k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7)
      | ~ m1_pre_topc(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X6,X4,X7,X5] :
      ( k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7)
      | ~ m1_pre_topc(X7,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_1(X6) ) ),
    inference(superposition,[],[f67,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f266,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f265,f48])).

fof(f265,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f264,f49])).

fof(f264,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f263,f50])).

fof(f263,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f262,f51])).

fof(f262,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f261,f52])).

fof(f261,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f260,f53])).

fof(f260,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f259,f59])).

fof(f59,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f259,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f258,f91])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f60,f62])).

fof(f62,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f258,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f248,f90])).

fof(f90,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f61,f63])).

fof(f63,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f248,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f239,f126])).

fof(f126,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f125,f48])).

fof(f125,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f123,f50])).

fof(f123,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f121,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f120,f53])).

fof(f120,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f119,f59])).

fof(f119,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f118,f91])).

fof(f118,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f117,f90])).

fof(f117,plain,
    ( ~ r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f116,f88])).

fof(f88,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f87,f62])).

fof(f87,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f66,f63])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f115,f45])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f46])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f47])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f54])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f55])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f57])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f83,f58])).

fof(f83,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( ( X5 = X7
                                      & X5 = X6 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                    <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f238,f45])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f46])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f47])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f54])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f55])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f56])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f57])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f85,f58])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f386,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f385,f93])).

fof(f385,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f374,f72])).

fof(f374,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f373,f89])).

fof(f89,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f64,f62])).

fof(f64,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f373,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f372,f48])).

fof(f372,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f371,f49])).

fof(f371,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f370,f50])).

fof(f370,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f369,f51])).

fof(f369,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f368,f52])).

fof(f368,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f367,f53])).

fof(f367,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f366,f59])).

fof(f366,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f365,f91])).

fof(f365,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f358,f90])).

fof(f358,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(resolution,[],[f357,f86])).

fof(f86,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(backward_demodulation,[],[f65,f63])).

fof(f65,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f357,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f356,f45])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f355,f46])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f354,f47])).

fof(f354,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f351,f104])).

fof(f351,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f343,f108])).

fof(f343,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f342,f45])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f341,f46])).

fof(f341,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f340,f47])).

fof(f340,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f339,f54])).

fof(f339,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f338,f55])).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f337,f56])).

fof(f337,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f332,f57])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f81,f58])).

fof(f81,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (30769)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.43  % (30769)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f390,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f389,f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(resolution,[],[f75,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f40,f39,f38,f37,f36,f35,f34,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f10])).
% 0.21/0.43  fof(f10,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.43  fof(f389,plain,(
% 0.21/0.43    ~v1_relat_1(sK2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f388,f96])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.21/0.43    inference(resolution,[],[f76,f53])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.43  fof(f388,plain,(
% 0.21/0.43    ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(resolution,[],[f387,f73])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.43  fof(f387,plain,(
% 0.21/0.43    ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))),
% 0.21/0.43    inference(subsumption_resolution,[],[f386,f284])).
% 0.21/0.43  fof(f284,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))),
% 0.21/0.43    inference(subsumption_resolution,[],[f283,f93])).
% 0.21/0.43  fof(f283,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f282])).
% 0.21/0.43  fof(f282,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(superposition,[],[f281,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.43  fof(f281,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f280,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f280,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f279,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    v2_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f279,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f278,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f278,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f277,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ~v2_struct_0(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f277,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f276,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    v2_pre_topc(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f276,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f275,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    l1_pre_topc(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f275,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f274,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    v1_funct_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f274,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f273,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f273,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f272,f53])).
% 0.21/0.43  fof(f272,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f271,f104])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f103,f45])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f102,f47])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f101,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ~v2_struct_0(sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f100,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    m1_pre_topc(sK3,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f99,f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ~v2_struct_0(sK4)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f98,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    m1_pre_topc(sK4,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f78,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.21/0.43  fof(f271,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f266,f108])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ( ! [X6,X4,X7,X5] : (k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7) | ~m1_pre_topc(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    ( ! [X6,X4,X7,X5] : (k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7) | ~m1_pre_topc(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_1(X6)) )),
% 0.21/0.43    inference(superposition,[],[f67,f79])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.43    inference(flattening,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.43  fof(f266,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f265,f48])).
% 0.21/0.43  fof(f265,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f264,f49])).
% 0.21/0.43  fof(f264,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f263,f50])).
% 0.21/0.43  fof(f263,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f262,f51])).
% 0.21/0.43  fof(f262,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f261,f52])).
% 0.21/0.43  fof(f261,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f260,f53])).
% 0.21/0.43  fof(f260,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f259,f59])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f259,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f258,f91])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.43    inference(forward_demodulation,[],[f60,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    sK5 = sK6),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f258,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f248,f90])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.21/0.43    inference(forward_demodulation,[],[f61,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    sK5 = sK7),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f248,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f245])).
% 0.21/0.43  fof(f245,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(resolution,[],[f239,f126])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f125,f48])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f124,f49])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f123,f50])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f121,f52])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f120,f53])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f119,f59])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f118,f91])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f117,f90])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    ~r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(resolution,[],[f116,f88])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(backward_demodulation,[],[f87,f62])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(backward_demodulation,[],[f66,f63])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f115,f45])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f114,f46])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f113,f47])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f112,f54])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f111,f55])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f110,f56])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f109,f57])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(superposition,[],[f83,f58])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).
% 0.21/0.43  fof(f239,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f238,f45])).
% 0.21/0.43  fof(f238,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f237,f46])).
% 0.21/0.43  fof(f237,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f236,f47])).
% 0.21/0.43  fof(f236,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f235,f54])).
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f234,f55])).
% 0.21/0.43  fof(f234,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f233,f56])).
% 0.21/0.43  fof(f233,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f230,f57])).
% 0.21/0.43  fof(f230,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(superposition,[],[f85,f58])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f43])).
% 0.21/0.43  fof(f386,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))),
% 0.21/0.43    inference(subsumption_resolution,[],[f385,f93])).
% 0.21/0.43  fof(f385,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f384])).
% 0.21/0.43  fof(f384,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,sK2,sK5) | r1_tmap_1(sK0,sK1,sK2,sK5) | ~r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(superposition,[],[f374,f72])).
% 0.21/0.43  fof(f374,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f373,f89])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(backward_demodulation,[],[f64,f62])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f373,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f372,f48])).
% 0.21/0.43  fof(f372,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f371,f49])).
% 0.21/0.43  fof(f371,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f370,f50])).
% 0.21/0.43  fof(f370,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f369,f51])).
% 0.21/0.43  fof(f369,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f368,f52])).
% 0.21/0.43  fof(f368,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f367,f53])).
% 0.21/0.43  fof(f367,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f366,f59])).
% 0.21/0.43  fof(f366,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f365,f91])).
% 0.21/0.43  fof(f365,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f358,f90])).
% 0.21/0.43  fof(f358,plain,(
% 0.21/0.43    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(resolution,[],[f357,f86])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(backward_demodulation,[],[f65,f63])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f357,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f356,f45])).
% 0.21/0.43  fof(f356,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f355,f46])).
% 0.21/0.43  fof(f355,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f354,f47])).
% 0.21/0.43  fof(f354,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f351,f104])).
% 0.21/0.43  fof(f351,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f350])).
% 0.21/0.44  fof(f350,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(superposition,[],[f343,f108])).
% 0.21/0.44  fof(f343,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f342,f45])).
% 0.21/0.44  fof(f342,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f341,f46])).
% 0.21/0.44  fof(f341,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f340,f47])).
% 0.21/0.44  fof(f340,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f339,f54])).
% 0.21/0.44  fof(f339,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f338,f55])).
% 0.21/0.44  fof(f338,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f337,f56])).
% 0.21/0.44  fof(f337,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f332,f57])).
% 0.21/0.44  fof(f332,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(superposition,[],[f81,f58])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f43])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (30769)------------------------------
% 0.21/0.44  % (30769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30769)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (30769)Memory used [KB]: 1918
% 0.21/0.44  % (30769)Time elapsed: 0.041 s
% 0.21/0.44  % (30769)------------------------------
% 0.21/0.44  % (30769)------------------------------
% 0.21/0.44  % (30750)Success in time 0.086 s
%------------------------------------------------------------------------------

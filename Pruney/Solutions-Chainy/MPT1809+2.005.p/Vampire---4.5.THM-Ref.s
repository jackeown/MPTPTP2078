%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  238 (2634 expanded)
%              Number of leaves         :   23 (1330 expanded)
%              Depth                    :   34
%              Number of atoms          : 2030 (61096 expanded)
%              Number of equality atoms :  132 (9010 expanded)
%              Maximal formula depth    :   30 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f98,f212,f244,f247,f367,f428,f454])).

fof(f454,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f452,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f452,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f451,f101])).

fof(f101,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f56,f58])).

fof(f58,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f451,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f450,f102])).

fof(f102,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f57,f59])).

fof(f59,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f450,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f449,f86])).

fof(f86,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_1
  <=> r1_tmap_1(sK0,sK1,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f449,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f382,f437])).

fof(f437,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | spl8_2 ),
    inference(forward_demodulation,[],[f91,f58])).

fof(f91,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_2
  <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f382,plain,
    ( ! [X4] :
        ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f381,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f381,plain,
    ( ! [X4] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f380,f45])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f380,plain,
    ( ! [X4] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f379,f46])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f379,plain,
    ( ! [X4] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f378,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f378,plain,
    ( ! [X4] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f377,f48])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f377,plain,
    ( ! [X4] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f360,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f360,plain,
    ( ! [X4] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X4)
        | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(superposition,[],[f112,f341])).

fof(f341,plain,
    ( sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f340,f47])).

fof(f340,plain,
    ( sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f339,f48])).

fof(f339,plain,
    ( sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f338,f49])).

fof(f338,plain,
    ( sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f337,f194])).

fof(f194,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl8_4
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f337,plain,
    ( sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f334,f99])).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f43,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f334,plain,
    ( ~ l1_struct_0(sK0)
    | sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f182,f243])).

fof(f243,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl8_8
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f182,plain,(
    ! [X10,X9] :
      ( ~ r2_funct_2(u1_struct_0(X9),u1_struct_0(sK1),X10,k2_tmap_1(sK0,sK1,sK2,X9))
      | ~ l1_struct_0(X9)
      | k2_tmap_1(sK0,sK1,sK2,X9) = X10
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X9),u1_struct_0(X9),u1_struct_0(sK1))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
      | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f166,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f135,f99])).

fof(f135,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f100])).

fof(f100,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f46,f63])).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f48])).

fof(f127,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f166,plain,(
    ! [X10,X9] :
      ( ~ l1_struct_0(X9)
      | ~ r2_funct_2(u1_struct_0(X9),u1_struct_0(sK1),X10,k2_tmap_1(sK0,sK1,sK2,X9))
      | k2_tmap_1(sK0,sK1,sK2,X9) = X10
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X9),u1_struct_0(X9),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
      | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
      | ~ v1_funct_1(X10) ) ),
    inference(resolution,[],[f140,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f140,plain,(
    ! [X1] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f139,f99])).

fof(f139,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f100])).

fof(f138,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f47])).

fof(f137,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f128,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f112,plain,(
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
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f111,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
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
    inference(subsumption_resolution,[],[f110,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
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
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,(
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
    inference(subsumption_resolution,[],[f108,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
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
    inference(subsumption_resolution,[],[f107,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,(
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
    inference(subsumption_resolution,[],[f106,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,(
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
    inference(subsumption_resolution,[],[f103,f53])).

fof(f53,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
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
    inference(superposition,[],[f81,f54])).

fof(f54,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f428,plain,
    ( ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f426,f55])).

fof(f426,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f425,f101])).

fof(f425,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f424,f102])).

fof(f424,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f421,f86])).

fof(f421,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f376,f390])).

fof(f390,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | spl8_3 ),
    inference(forward_demodulation,[],[f95,f59])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_3
  <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f376,plain,
    ( ! [X3] :
        ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f375,f44])).

fof(f375,plain,
    ( ! [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f374,f45])).

fof(f374,plain,
    ( ! [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f373,f46])).

fof(f373,plain,
    ( ! [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f372,f47])).

fof(f372,plain,
    ( ! [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f371,f48])).

fof(f371,plain,
    ( ! [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f359,f49])).

fof(f359,plain,
    ( ! [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(superposition,[],[f119,f341])).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f118,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f52])).

fof(f113,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f79,f54])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f367,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f351,f87])).

fof(f87,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f351,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f274,f341])).

fof(f274,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f273,f44])).

fof(f273,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f272,f45])).

fof(f272,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f271,f46])).

fof(f271,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f270,f47])).

fof(f270,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f269,f48])).

fof(f269,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f268,f49])).

fof(f268,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f267,f55])).

fof(f267,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f266,f101])).

fof(f266,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f265,f102])).

fof(f265,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f264,f158])).

fof(f158,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f90,f58])).

fof(f90,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f264,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
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
    | ~ spl8_3 ),
    inference(resolution,[],[f126,f161])).

fof(f161,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f94,f59])).

fof(f94,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f126,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f43])).

fof(f123,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f122,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f51])).

fof(f121,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f52])).

fof(f120,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f105,f53])).

fof(f105,plain,(
    ! [X6,X8,X7] :
      ( r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8)
      | ~ r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8)
      | ~ r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK4))
      | ~ m1_subset_1(X8,u1_struct_0(sK3))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f77,f54])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f247,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl8_7 ),
    inference(subsumption_resolution,[],[f245,f43])).

fof(f245,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_7 ),
    inference(resolution,[],[f239,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f239,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl8_7
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f244,plain,
    ( ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f235,f241,f237])).

fof(f235,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0) ),
    inference(subsumption_resolution,[],[f234,f42])).

fof(f234,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f233,f43])).

fof(f233,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f232,f44])).

fof(f232,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f231,f45])).

fof(f231,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f230,f46])).

fof(f230,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f229,f41])).

fof(f229,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f228,f47])).

fof(f228,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f227,f48])).

fof(f227,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f226,f49])).

fof(f226,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f66,f222])).

fof(f222,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK0) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2) ),
    inference(forward_demodulation,[],[f221,f187])).

fof(f187,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f184,f43])).

fof(f184,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f148,f64])).

fof(f148,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f42])).

fof(f146,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f43])).

fof(f145,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f144,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f45])).

fof(f143,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f46])).

fof(f142,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f47])).

fof(f141,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f48])).

fof(f129,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f67])).

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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f221,plain,(
    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f218,f43])).

fof(f218,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f217,f64])).

fof(f217,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f216,f41])).

fof(f216,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f42])).

fof(f215,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f214,f43])).

fof(f214,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f153,f64])).

fof(f153,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(sK0,X4)
      | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X3,sK0)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f152,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK0,X4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f151,f45])).

fof(f151,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK0,X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f150,f46])).

fof(f150,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK0,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f149,f47])).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK0,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f130,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(sK0,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f49,f65])).

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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
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
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
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
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f212,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f210,f100])).

fof(f210,plain,
    ( ~ l1_struct_0(sK1)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f209,f47])).

fof(f209,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f208,f48])).

fof(f208,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f207,f49])).

fof(f207,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f206,f99])).

fof(f206,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl8_4 ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | spl8_4 ),
    inference(resolution,[],[f195,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f195,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f98,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f60,f89,f85])).

fof(f60,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f61,f93,f85])).

fof(f61,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f62,f93,f89,f85])).

fof(f62,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (32219)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (32211)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (32207)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (32227)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (32208)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (32213)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (32206)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (32206)Refutation not found, incomplete strategy% (32206)------------------------------
% 0.21/0.51  % (32206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32207)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (32230)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (32231)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (32221)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (32206)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32206)Memory used [KB]: 10746
% 0.21/0.51  % (32206)Time elapsed: 0.088 s
% 0.21/0.51  % (32206)------------------------------
% 0.21/0.51  % (32206)------------------------------
% 0.21/0.51  % (32220)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (32218)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (32222)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (32225)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (32223)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (32214)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (32228)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (32212)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (32209)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (32210)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (32212)Refutation not found, incomplete strategy% (32212)------------------------------
% 0.21/0.53  % (32212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32226)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (32212)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32212)Memory used [KB]: 10746
% 0.21/0.53  % (32212)Time elapsed: 0.074 s
% 0.21/0.53  % (32212)------------------------------
% 0.21/0.53  % (32212)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f455,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f96,f97,f98,f212,f244,f247,f367,f428,f454])).
% 0.21/0.54  fof(f454,plain,(
% 0.21/0.54    ~spl8_1 | spl8_2 | ~spl8_4 | ~spl8_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f453])).
% 0.21/0.54  fof(f453,plain,(
% 0.21/0.54    $false | (~spl8_1 | spl8_2 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f452,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.21/0.54  fof(f452,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,u1_struct_0(sK0)) | (~spl8_1 | spl8_2 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f451,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f56,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    sK5 = sK6),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | (~spl8_1 | spl8_2 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f450,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.21/0.54    inference(forward_demodulation,[],[f57,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    sK5 = sK7),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | (~spl8_1 | spl8_2 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f449,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,sK2,sK5) | ~spl8_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    spl8_1 <=> r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.54  fof(f449,plain,(
% 0.21/0.54    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | (spl8_2 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(resolution,[],[f382,f437])).
% 0.21/0.54  fof(f437,plain,(
% 0.21/0.54    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | spl8_2),
% 0.21/0.54    inference(forward_demodulation,[],[f91,f58])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | spl8_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl8_2 <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    ( ! [X4] : (r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~r1_tmap_1(sK0,sK1,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f381,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ( ! [X4] : (~r1_tmap_1(sK0,sK1,sK2,X4) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f380,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    v2_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    ( ! [X4] : (~r1_tmap_1(sK0,sK1,sK2,X4) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f379,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    ( ! [X4] : (~r1_tmap_1(sK0,sK1,sK2,X4) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f378,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    ( ! [X4] : (~r1_tmap_1(sK0,sK1,sK2,X4) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f377,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f377,plain,(
% 0.21/0.54    ( ! [X4] : (~r1_tmap_1(sK0,sK1,sK2,X4) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f360,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    ( ! [X4] : (~r1_tmap_1(sK0,sK1,sK2,X4) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(superposition,[],[f112,f341])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f340,f47])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | ~v1_funct_1(sK2) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f339,f48])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f338,f49])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f337,f194])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f193])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    spl8_4 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl8_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f334,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    l1_struct_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f43,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    ~l1_struct_0(sK0) | sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl8_8),
% 0.21/0.54    inference(resolution,[],[f182,f243])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~spl8_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f241])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    spl8_8 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X10,X9] : (~r2_funct_2(u1_struct_0(X9),u1_struct_0(sK1),X10,k2_tmap_1(sK0,sK1,sK2,X9)) | ~l1_struct_0(X9) | k2_tmap_1(sK0,sK1,sK2,X9) = X10 | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X9),u1_struct_0(X9),u1_struct_0(sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1)))) | ~v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1)) | ~v1_funct_1(X10)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f166,f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f135,f99])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f134,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    l1_struct_0(sK1)),
% 0.21/0.54    inference(resolution,[],[f46,f63])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f133,f47])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f127,f48])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f49,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X10,X9] : (~l1_struct_0(X9) | ~r2_funct_2(u1_struct_0(X9),u1_struct_0(sK1),X10,k2_tmap_1(sK0,sK1,sK2,X9)) | k2_tmap_1(sK0,sK1,sK2,X9) = X10 | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X9),u1_struct_0(X9),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X9)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1)))) | ~v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1)) | ~v1_funct_1(X10)) )),
% 0.21/0.54    inference(resolution,[],[f140,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~l1_struct_0(X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f139,f99])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f138,f100])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f137,f47])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f128,f48])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X1] : (~l1_struct_0(X1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f49,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f111,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f109,f43])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f108,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~v2_struct_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f107,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f106,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~v2_struct_0(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f103,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    m1_pre_topc(sK4,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(superposition,[],[f81,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).
% 0.21/0.54  fof(f428,plain,(
% 0.21/0.54    ~spl8_1 | spl8_3 | ~spl8_4 | ~spl8_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f427])).
% 0.21/0.54  fof(f427,plain,(
% 0.21/0.54    $false | (~spl8_1 | spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f426,f55])).
% 0.21/0.54  fof(f426,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,u1_struct_0(sK0)) | (~spl8_1 | spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f425,f101])).
% 0.21/0.54  fof(f425,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | (~spl8_1 | spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f424,f102])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | (~spl8_1 | spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f421,f86])).
% 0.21/0.54  fof(f421,plain,(
% 0.21/0.54    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | (spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(resolution,[],[f376,f390])).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | spl8_3),
% 0.21/0.54    inference(forward_demodulation,[],[f95,f59])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | spl8_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl8_3 <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    ( ! [X3] : (r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~r1_tmap_1(sK0,sK1,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f375,f44])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f374,f45])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f373,f46])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f372,f47])).
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f371,f48])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f359,f49])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X3) | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(superposition,[],[f119,f341])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f118,f41])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f42])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f116,f43])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f50])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f51])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f113,f52])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f104,f53])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(superposition,[],[f79,f54])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f367,plain,(
% 0.21/0.54    spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    $false | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f351,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ~r1_tmap_1(sK0,sK1,sK2,sK5) | spl8_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f85])).
% 0.21/0.54  fof(f351,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,sK2,sK5) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.21/0.54    inference(backward_demodulation,[],[f274,f341])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f273,f44])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f272,f45])).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f271,f46])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f270,f47])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f269,f48])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f268,f49])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f267,f55])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f266,f101])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f265,f102])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f264,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~spl8_2),
% 0.21/0.54    inference(forward_demodulation,[],[f90,f58])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~spl8_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f89])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl8_3),
% 0.21/0.54    inference(resolution,[],[f126,f161])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~spl8_3),
% 0.21/0.54    inference(forward_demodulation,[],[f94,f59])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~spl8_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f93])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f41])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f42])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f43])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f122,f50])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f121,f51])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f120,f52])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f105,f53])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r1_tmap_1(sK0,X6,k2_tmap_1(sK0,X6,X7,sK0),X8) | ~r1_tmap_1(sK4,X6,k2_tmap_1(sK0,X6,X7,sK4),X8) | ~r1_tmap_1(sK3,X6,k2_tmap_1(sK0,X6,X7,sK3),X8) | ~m1_subset_1(X8,u1_struct_0(sK4)) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(superposition,[],[f77,f54])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    spl8_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    $false | spl8_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f245,f43])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | spl8_7),
% 0.21/0.54    inference(resolution,[],[f239,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ~m1_pre_topc(sK0,sK0) | spl8_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f237])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    spl8_7 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    ~spl8_7 | spl8_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f235,f241,f237])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f234,f42])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f233,f43])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f44])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f231,f45])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f230,f46])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f229,f41])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f228,f47])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f227,f48])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f226,f49])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f225])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(superposition,[],[f66,f222])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    k2_tmap_1(sK0,sK1,sK2,sK0) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f221,f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    k2_tmap_1(sK0,sK1,sK2,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f184,f43])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    k2_tmap_1(sK0,sK1,sK2,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.54    inference(resolution,[],[f148,f64])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f147,f41])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f42])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f43])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f44])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f143,f45])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f142,f46])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f47])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f129,f48])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k2_tmap_1(sK0,sK1,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f49,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f218,f43])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.54    inference(resolution,[],[f217,f64])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f216,f41])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f42])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f214,f43])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f213])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f153,f64])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_pre_topc(sK0,X4) | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X3,sK0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f152,f44])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_pre_topc(X3,sK0) | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK0,X4) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f151,f45])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_pre_topc(X3,sK0) | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK0,X4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f46])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_pre_topc(X3,sK0) | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK0,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f149,f47])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_pre_topc(X3,sK0) | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK0,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f48])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_pre_topc(X3,sK0) | k3_tmap_1(X4,sK1,sK0,X3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X3)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(sK0,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.54    inference(resolution,[],[f49,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    spl8_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    $false | spl8_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f210,f100])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    ~l1_struct_0(sK1) | spl8_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f209,f47])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | spl8_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f208,f48])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | spl8_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f207,f49])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | spl8_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f206,f99])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ~l1_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | spl8_4),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f205])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ~l1_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0) | spl8_4),
% 0.21/0.54    inference(resolution,[],[f195,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) | spl8_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f193])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl8_1 | spl8_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f60,f89,f85])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl8_1 | spl8_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f61,f93,f85])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f62,f93,f89,f85])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (32207)------------------------------
% 0.21/0.54  % (32207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32207)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (32207)Memory used [KB]: 11001
% 0.21/0.54  % (32207)Time elapsed: 0.093 s
% 0.21/0.54  % (32207)------------------------------
% 0.21/0.54  % (32207)------------------------------
% 0.21/0.54  % (32216)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (32205)Success in time 0.178 s
%------------------------------------------------------------------------------

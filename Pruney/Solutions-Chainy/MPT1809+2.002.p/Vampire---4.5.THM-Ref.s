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
% DateTime   : Thu Dec  3 13:19:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  198 (1953 expanded)
%              Number of leaves         :   19 ( 989 expanded)
%              Depth                    :   43
%              Number of atoms          : 1825 (46088 expanded)
%              Number of equality atoms :   99 (6775 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f89,f91,f248,f303,f350])).

fof(f350,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f348,f96])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f35,f34,f33,f32,f31,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

% (32623)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f348,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f347,f97])).

fof(f97,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f347,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f346,f87])).

fof(f87,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_1
  <=> r1_tmap_1(sK0,sK1,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f346,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | spl8_3 ),
    inference(superposition,[],[f318,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f318,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f317,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f317,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f316,f43])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f316,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f315,f44])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f315,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f314,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f314,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f313,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f313,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f312,f47])).

fof(f312,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f311,f53])).

fof(f53,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f311,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f310,f93])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f54,f56])).

fof(f56,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f310,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f308,f92])).

fof(f92,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f55,f57])).

fof(f57,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f308,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_3 ),
    inference(resolution,[],[f304,f190])).

fof(f190,plain,(
    ! [X4,X5,X3] :
      ( r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5)
      | ~ r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f189,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f189,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5)
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
    inference(subsumption_resolution,[],[f188,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f188,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5)
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
    inference(subsumption_resolution,[],[f187,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f187,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5)
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
    inference(subsumption_resolution,[],[f161,f105])).

fof(f105,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f104,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f103,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f51])).

fof(f51,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f69,f52])).

fof(f52,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f161,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5)
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
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5)
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
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f117,f109])).

fof(f109,plain,(
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
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
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
    inference(superposition,[],[f61,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f61,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f117,plain,(
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
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f116,f39])).

fof(f116,plain,(
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
    inference(subsumption_resolution,[],[f115,f40])).

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
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f41])).

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
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f48])).

fof(f113,plain,(
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
    inference(subsumption_resolution,[],[f112,f49])).

fof(f112,plain,(
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
    inference(subsumption_resolution,[],[f111,f50])).

fof(f111,plain,(
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
    inference(subsumption_resolution,[],[f110,f51])).

fof(f110,plain,(
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
    inference(superposition,[],[f74,f52])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f38])).

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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).

fof(f304,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | spl8_3 ),
    inference(forward_demodulation,[],[f85,f57])).

fof(f85,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_3
  <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f303,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f301,f96])).

fof(f301,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f300,f97])).

fof(f300,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f299,f87])).

fof(f299,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | spl8_2 ),
    inference(superposition,[],[f276,f65])).

fof(f276,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f275,f42])).

fof(f275,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f274,f43])).

fof(f274,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f273,f44])).

fof(f273,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f272,f45])).

fof(f272,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f271,f46])).

fof(f271,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f270,f47])).

fof(f270,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f269,f53])).

fof(f269,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f268,f93])).

fof(f268,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f266,f92])).

fof(f266,plain,
    ( ~ r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_2 ),
    inference(resolution,[],[f265,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2)
      | ~ r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f185,f39])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
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
    inference(subsumption_resolution,[],[f184,f40])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
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
    inference(subsumption_resolution,[],[f183,f41])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
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
    inference(subsumption_resolution,[],[f162,f105])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
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
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2)
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
    inference(superposition,[],[f125,f109])).

fof(f125,plain,(
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
    inference(subsumption_resolution,[],[f124,f39])).

fof(f124,plain,(
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
    inference(subsumption_resolution,[],[f123,f40])).

fof(f123,plain,(
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
    inference(subsumption_resolution,[],[f122,f41])).

fof(f122,plain,(
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
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,(
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
    inference(subsumption_resolution,[],[f120,f49])).

fof(f120,plain,(
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
    inference(subsumption_resolution,[],[f119,f50])).

fof(f119,plain,(
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
    inference(subsumption_resolution,[],[f118,f51])).

fof(f118,plain,(
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
    inference(superposition,[],[f76,f52])).

% (32628)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f76,plain,(
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
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f265,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | spl8_2 ),
    inference(forward_demodulation,[],[f82,f56])).

fof(f82,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_2
  <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f248,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f246,f96])).

fof(f246,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f245,f97])).

fof(f245,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f244,f79])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f244,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(superposition,[],[f228,f65])).

fof(f228,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f227,f39])).

fof(f227,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f226,f40])).

fof(f226,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f225,f41])).

fof(f225,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f224,f42])).

fof(f224,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f223,f43])).

fof(f223,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f222,f44])).

fof(f222,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f221,f45])).

fof(f221,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f220,f46])).

fof(f220,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f219,f47])).

fof(f219,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f218,f105])).

fof(f218,plain,
    ( r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(superposition,[],[f148,f109])).

fof(f148,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f147,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f146,f43])).

fof(f146,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f145,f44])).

fof(f145,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f143,f46])).

fof(f143,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f142,f47])).

fof(f142,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f141,plain,
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
    inference(subsumption_resolution,[],[f140,f93])).

fof(f140,plain,
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
    inference(subsumption_resolution,[],[f139,f92])).

fof(f139,plain,
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
    inference(subsumption_resolution,[],[f138,f95])).

fof(f95,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f90,f56])).

fof(f90,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f138,plain,
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
    inference(resolution,[],[f137,f94])).

fof(f94,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f88,f57])).

fof(f88,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2)
      | r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2)
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
    inference(subsumption_resolution,[],[f136,f39])).

fof(f136,plain,(
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
    inference(subsumption_resolution,[],[f135,f40])).

fof(f135,plain,(
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
    inference(subsumption_resolution,[],[f134,f41])).

fof(f134,plain,(
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
    inference(subsumption_resolution,[],[f133,f48])).

fof(f133,plain,(
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
    inference(subsumption_resolution,[],[f132,f49])).

% (32620)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f132,plain,(
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
    inference(subsumption_resolution,[],[f131,f50])).

fof(f131,plain,(
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
    inference(subsumption_resolution,[],[f128,f51])).

fof(f128,plain,(
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
    inference(superposition,[],[f72,f52])).

fof(f72,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f58,f81,f78])).

fof(f58,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f59,f84,f78])).

fof(f59,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f60,f84,f81,f78])).

fof(f60,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (32611)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (32611)Refutation not found, incomplete strategy% (32611)------------------------------
% 0.20/0.47  % (32611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (32613)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (32624)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (32619)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (32617)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (32611)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (32611)Memory used [KB]: 6268
% 0.20/0.47  % (32611)Time elapsed: 0.054 s
% 0.20/0.47  % (32611)------------------------------
% 0.20/0.47  % (32611)------------------------------
% 0.20/0.48  % (32629)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (32612)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (32616)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (32625)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (32613)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f86,f89,f91,f248,f303,f350])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    ~spl8_1 | spl8_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f349])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    $false | (~spl8_1 | spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f348,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f66,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f35,f34,f33,f32,f31,f30,f29,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  % (32623)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (~spl8_1 | spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f347,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(resolution,[],[f67,f47])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | (~spl8_1 | spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f346,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,sK2,sK5) | ~spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl8_1 <=> r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.49  fof(f346,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | spl8_3),
% 0.20/0.49    inference(superposition,[],[f318,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.49  fof(f318,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f317,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f316,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v2_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f315,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f314,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f313,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f313,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f312,f47])).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f311,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f310,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f54,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    sK5 = sK6),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f310,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f308,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.49    inference(forward_demodulation,[],[f55,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    sK5 = sK7),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_3),
% 0.20/0.49    inference(resolution,[],[f304,f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f189,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f188,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f187,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f161,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f104,f39])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f41])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f102,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f100,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~v2_struct_0(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f99,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    m1_pre_topc(sK4,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f69,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k7_relat_1(X4,u1_struct_0(sK0)),X5) | r1_tmap_1(sK4,X3,k2_tmap_1(sK0,X3,X4,sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f117,f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5] : (k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7) | ~m1_pre_topc(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5] : (k7_relat_1(X6,u1_struct_0(X7)) = k2_tmap_1(X4,X5,X6,X7) | ~m1_pre_topc(X7,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_1(X6)) )),
% 0.20/0.49    inference(superposition,[],[f61,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f39])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f40])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f41])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f113,f48])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f112,f49])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f50])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f51])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f74,f52])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | spl8_3),
% 0.20/0.49    inference(forward_demodulation,[],[f85,f57])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl8_3 <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    ~spl8_1 | spl8_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    $false | (~spl8_1 | spl8_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f301,f96])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (~spl8_1 | spl8_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f300,f97])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | (~spl8_1 | spl8_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f299,f87])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,sK2,sK5) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | spl8_2),
% 0.20/0.49    inference(superposition,[],[f276,f65])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f275,f42])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f274,f43])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f273,f44])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f272,f45])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f271,f46])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f270,f47])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f269,f53])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f268,f93])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f266,f92])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_2),
% 0.20/0.49    inference(resolution,[],[f265,f186])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f185,f39])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f184,f40])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f183,f41])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f162,f105])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k7_relat_1(X1,u1_struct_0(sK0)),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f125,f109])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f39])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f123,f40])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f122,f41])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f121,f48])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f120,f49])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f119,f50])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f51])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f76,f52])).
% 0.20/0.49  % (32628)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | spl8_2),
% 0.20/0.49    inference(forward_demodulation,[],[f82,f56])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl8_2 <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f247])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    $false | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f246,f96])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f245,f97])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f244,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,sK2,sK5) | spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f78])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,sK2,sK5) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(superposition,[],[f228,f65])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f227,f39])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f226,f40])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f225,f41])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f224,f42])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f223,f43])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f222,f44])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f221,f45])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f220,f46])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f219,f47])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f218,f105])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k7_relat_1(sK2,u1_struct_0(sK0)),sK5) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(superposition,[],[f148,f109])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f147,f42])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f146,f43])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f145,f44])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f144,f45])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f143,f46])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f142,f47])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f53])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f140,f93])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f139,f92])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f138,f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~spl8_2),
% 0.20/0.49    inference(forward_demodulation,[],[f90,f56])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK5) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl8_3),
% 0.20/0.49    inference(resolution,[],[f137,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~spl8_3),
% 0.20/0.49    inference(forward_demodulation,[],[f88,f57])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f39])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f135,f40])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f41])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f133,f48])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f132,f49])).
% 0.20/0.49  % (32620)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f131,f50])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f128,f51])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tmap_1(sK0,X0,k2_tmap_1(sK0,X0,X1,sK0),X2) | ~r1_tmap_1(sK4,X0,k2_tmap_1(sK0,X0,X1,sK4),X2) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK0,X0,X1,sK3),X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f72,f52])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl8_1 | spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f81,f78])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl8_1 | spl8_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f59,f84,f78])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f60,f84,f81,f78])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (32613)------------------------------
% 0.20/0.49  % (32613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (32613)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (32613)Memory used [KB]: 10874
% 0.20/0.49  % (32613)Time elapsed: 0.080 s
% 0.20/0.49  % (32613)------------------------------
% 0.20/0.49  % (32613)------------------------------
% 0.20/0.50  % (32610)Success in time 0.137 s
%------------------------------------------------------------------------------

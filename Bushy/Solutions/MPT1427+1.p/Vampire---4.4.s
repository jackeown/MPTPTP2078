%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t22_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:07 EDT 2019

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  404 (4243 expanded)
%              Number of leaves         :   65 (2222 expanded)
%              Depth                    :   31
%              Number of atoms          : 1758 (49094 expanded)
%              Number of equality atoms :  170 (5407 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f785,f834,f1078,f1093,f1328,f1330,f5397,f5456,f5667,f5708,f5713,f5826,f6149,f6947,f6997,f7048,f7094,f7121,f7368,f8388,f9116,f9122,f9156,f9253,f9258,f9281,f9329,f9335,f9417])).

fof(f9417,plain,
    ( ~ spl10_104
    | spl10_991 ),
    inference(avatar_contradiction_clause,[],[f9416])).

fof(f9416,plain,
    ( $false
    | ~ spl10_104
    | ~ spl10_991 ),
    inference(subsumption_resolution,[],[f9415,f91])).

fof(f91,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,sK1)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f79,f78,f77,f76,f75,f74,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                                    & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                    & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                    & v1_funct_1(X7) )
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                                & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,X1) )
                        & m1_subset_1(X4,X1) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( k1_domain_1(sK0,X1,k4_binop_1(sK0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X6,X7),k1_domain_1(sK0,X1,X2,X4),k1_domain_1(sK0,X1,X3,X5))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                  & v1_funct_1(X7) )
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                              & v1_funct_2(X6,k2_zfmisc_1(sK0,sK0),sK0)
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,X1) )
                      & m1_subset_1(X4,X1) )
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                  & v1_funct_1(X7) )
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                              & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,X1) )
                      & m1_subset_1(X4,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( k1_domain_1(X0,sK1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(sK1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X6,X7),k1_domain_1(X0,sK1,X2,X4),k1_domain_1(X0,sK1,X3,X5))
                                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                                & v1_funct_2(X7,k2_zfmisc_1(sK1,sK1),sK1)
                                & v1_funct_1(X7) )
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                            & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,sK1) )
                    & m1_subset_1(X4,sK1) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                              & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X7) )
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                          & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X1) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,sK2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,sK2,X4),k1_domain_1(X0,X1,X3,X5))
                            & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X7) )
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,X1) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                          & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X7) )
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X1) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,sK3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,sK3,X5))
                        & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X7) )
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,X1) )
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                      & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X7) )
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X1) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,sK4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,sK4),k1_domain_1(X0,X1,X3,X5))
                    & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X7) )
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X6) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                  & v1_funct_1(X7) )
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X6) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( ? [X7] :
                ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,sK5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,sK5))
                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                & v1_funct_1(X7) )
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X6) )
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
              & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
              & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
              & v1_funct_1(X7) )
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
          & v1_funct_1(X6) )
     => ( ? [X7] :
            ( k1_domain_1(X0,X1,k4_binop_1(X0,sK6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,sK6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
            & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
            & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
            & v1_funct_1(X7) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(sK6,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
          & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
          & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
          & v1_funct_1(X7) )
     => ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,sK7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,sK7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(sK7,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                  & v1_funct_1(X7) )
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                              & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,X1) )
                      & m1_subset_1(X4,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) != k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                  & v1_funct_1(X7) )
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                              & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,X1) )
                      & m1_subset_1(X4,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ! [X4] :
                        ( m1_subset_1(X4,X1)
                       => ! [X5] :
                            ( m1_subset_1(X5,X1)
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                                  & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                                  & v1_funct_1(X6) )
                               => ! [X7] :
                                    ( ( m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                      & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                      & v1_funct_1(X7) )
                                   => k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) = k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => ! [X5] :
                          ( m1_subset_1(X5,X1)
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                                & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                                & v1_funct_1(X6) )
                             => ! [X7] :
                                  ( ( m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                    & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                    & v1_funct_1(X7) )
                                 => k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) = k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',t22_filter_1)).

fof(f9415,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | ~ spl10_104
    | ~ spl10_991 ),
    inference(subsumption_resolution,[],[f9414,f92])).

fof(f92,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f9414,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,sK1)
    | ~ spl10_104
    | ~ spl10_991 ),
    inference(trivial_inequality_removal,[],[f9413])).

fof(f9413,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,sK1)
    | ~ spl10_104
    | ~ spl10_991 ),
    inference(superposition,[],[f9328,f2911])).

fof(f2911,plain,
    ( ! [X2,X3] :
        ( k4_binop_1(sK1,sK7,X2,X3) = k1_binop_1(sK7,X2,X3)
        | ~ m1_subset_1(X3,sK1)
        | ~ m1_subset_1(X2,sK1) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f2910,f1572])).

fof(f1572,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ spl10_104 ),
    inference(backward_demodulation,[],[f1569,f97])).

fof(f97,plain,(
    v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f1569,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relat_1(sK7)
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f1566,f98])).

fof(f98,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f80])).

fof(f1566,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_104 ),
    inference(superposition,[],[f1092,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',redefinition_k1_relset_1)).

fof(f1092,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7)
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f1091,plain,
    ( spl10_104
  <=> k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f2910,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X3,sK1)
        | k4_binop_1(sK1,sK7,X2,X3) = k1_binop_1(sK7,X2,X3) )
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f2909,f1569])).

fof(f2909,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
        | k4_binop_1(sK1,sK7,X2,X3) = k1_binop_1(sK7,X2,X3) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f2908,f1573])).

fof(f1573,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ spl10_104 ),
    inference(backward_demodulation,[],[f1569,f98])).

fof(f2908,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X3,sK1)
        | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
        | k4_binop_1(sK1,sK7,X2,X3) = k1_binop_1(sK7,X2,X3) )
    | ~ spl10_104 ),
    inference(superposition,[],[f1547,f1569])).

fof(f1547,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X9,X9),X9)))
      | ~ m1_subset_1(X10,X9)
      | ~ m1_subset_1(X8,X9)
      | ~ v1_funct_2(sK7,k2_zfmisc_1(X9,X9),X9)
      | k4_binop_1(X9,sK7,X10,X8) = k1_binop_1(sK7,X10,X8) ) ),
    inference(resolution,[],[f132,f96])).

fof(f96,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f80])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',redefinition_k4_binop_1)).

fof(f9328,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ spl10_991 ),
    inference(avatar_component_clause,[],[f9327])).

fof(f9327,plain,
    ( spl10_991
  <=> k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_991])])).

fof(f9335,plain,
    ( ~ spl10_430
    | ~ spl10_436
    | spl10_631
    | spl10_663
    | ~ spl10_948
    | ~ spl10_952
    | spl10_989 ),
    inference(avatar_contradiction_clause,[],[f9334])).

fof(f9334,plain,
    ( $false
    | ~ spl10_430
    | ~ spl10_436
    | ~ spl10_631
    | ~ spl10_663
    | ~ spl10_948
    | ~ spl10_952
    | ~ spl10_989 ),
    inference(subsumption_resolution,[],[f9333,f9086])).

fof(f9086,plain,
    ( m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_948 ),
    inference(avatar_component_clause,[],[f9085])).

fof(f9085,plain,
    ( spl10_948
  <=> m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_948])])).

fof(f9333,plain,
    ( ~ m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_430
    | ~ spl10_436
    | ~ spl10_631
    | ~ spl10_663
    | ~ spl10_952
    | ~ spl10_989 ),
    inference(subsumption_resolution,[],[f9332,f9099])).

fof(f9099,plain,
    ( m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_952 ),
    inference(avatar_component_clause,[],[f9098])).

fof(f9098,plain,
    ( spl10_952
  <=> m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_952])])).

fof(f9332,plain,
    ( ~ m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_430
    | ~ spl10_436
    | ~ spl10_631
    | ~ spl10_663
    | ~ spl10_989 ),
    inference(resolution,[],[f9331,f7946])).

fof(f7946,plain,
    ( ! [X17,X18] :
        ( m1_subset_1(k4_tarski(X17,X18),k1_relat_1(k3_funct_4(sK6,sK7)))
        | ~ m1_subset_1(X18,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X17,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl10_430
    | ~ spl10_436
    | ~ spl10_663 ),
    inference(subsumption_resolution,[],[f7912,f6813])).

fof(f6813,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_663 ),
    inference(avatar_component_clause,[],[f6812])).

fof(f6812,plain,
    ( spl10_663
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_663])])).

fof(f7912,plain,
    ( ! [X17,X18] :
        ( m1_subset_1(k4_tarski(X17,X18),k1_relat_1(k3_funct_4(sK6,sK7)))
        | ~ m1_subset_1(X18,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X17,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl10_430
    | ~ spl10_436 ),
    inference(duplicate_literal_removal,[],[f7867])).

fof(f7867,plain,
    ( ! [X17,X18] :
        ( m1_subset_1(k4_tarski(X17,X18),k1_relat_1(k3_funct_4(sK6,sK7)))
        | ~ m1_subset_1(X18,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X17,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl10_430
    | ~ spl10_436 ),
    inference(superposition,[],[f553,f7786])).

fof(f7786,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relat_1(k3_funct_4(sK6,sK7))
    | ~ spl10_430
    | ~ spl10_436 ),
    inference(subsumption_resolution,[],[f7777,f4009])).

fof(f4009,plain,
    ( m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_430 ),
    inference(avatar_component_clause,[],[f4008])).

fof(f4008,plain,
    ( spl10_430
  <=> m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_430])])).

fof(f7777,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relat_1(k3_funct_4(sK6,sK7))
    | ~ m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_436 ),
    inference(superposition,[],[f4027,f115])).

fof(f4027,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))
    | ~ spl10_436 ),
    inference(avatar_component_clause,[],[f4026])).

fof(f4026,plain,
    ( spl10_436
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_436])])).

fof(f553,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_tarski(X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_tarski(X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f126,f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',redefinition_k1_domain_1)).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',dt_k1_domain_1)).

fof(f9331,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ spl10_631
    | ~ spl10_989 ),
    inference(subsumption_resolution,[],[f9330,f6203])).

fof(f6203,plain,
    ( ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ spl10_631 ),
    inference(avatar_component_clause,[],[f6202])).

fof(f6202,plain,
    ( spl10_631
  <=> ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_631])])).

fof(f9330,plain,
    ( v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ spl10_989 ),
    inference(resolution,[],[f9322,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',t2_subset)).

fof(f9322,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ spl10_989 ),
    inference(avatar_component_clause,[],[f9321])).

fof(f9321,plain,
    ( spl10_989
  <=> ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_989])])).

fof(f9329,plain,
    ( ~ spl10_989
    | ~ spl10_991
    | ~ spl10_100
    | ~ spl10_576
    | ~ spl10_578
    | spl10_979 ),
    inference(avatar_split_clause,[],[f9316,f9251,f5698,f5692,f1076,f9327,f9321])).

fof(f1076,plain,
    ( spl10_100
  <=> k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f5692,plain,
    ( spl10_576
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_576])])).

fof(f5698,plain,
    ( spl10_578
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_578])])).

fof(f9251,plain,
    ( spl10_979
  <=> k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_979])])).

fof(f9316,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ spl10_100
    | ~ spl10_576
    | ~ spl10_578
    | ~ spl10_979 ),
    inference(subsumption_resolution,[],[f9315,f5693])).

fof(f5693,plain,
    ( v1_relat_1(sK6)
    | ~ spl10_576 ),
    inference(avatar_component_clause,[],[f5692])).

fof(f9315,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_relat_1(sK6)
    | ~ spl10_100
    | ~ spl10_578
    | ~ spl10_979 ),
    inference(subsumption_resolution,[],[f9314,f93])).

fof(f93,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f9314,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl10_100
    | ~ spl10_578
    | ~ spl10_979 ),
    inference(subsumption_resolution,[],[f9313,f5699])).

fof(f5699,plain,
    ( v1_relat_1(sK7)
    | ~ spl10_578 ),
    inference(avatar_component_clause,[],[f5698])).

fof(f9313,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl10_100
    | ~ spl10_979 ),
    inference(subsumption_resolution,[],[f9312,f96])).

fof(f9312,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl10_100
    | ~ spl10_979 ),
    inference(superposition,[],[f9309,f133])).

fof(f133,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3)) = k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3))
      | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3)) = k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3))
          | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
          | ~ v1_funct_1(X5)
          | ~ v1_relat_1(X5) )
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3)) = k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3))
          | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
          | ~ v1_funct_1(X5)
          | ~ v1_relat_1(X5) )
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_relat_1(X4) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_relat_1(X5) )
         => ( r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
           => k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3)) = k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',t58_funct_4)).

fof(f9309,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ spl10_100
    | ~ spl10_979 ),
    inference(subsumption_resolution,[],[f9308,f89])).

fof(f89,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f9308,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl10_100
    | ~ spl10_979 ),
    inference(subsumption_resolution,[],[f9306,f90])).

fof(f90,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f9306,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl10_100
    | ~ spl10_979 ),
    inference(superposition,[],[f9252,f2870])).

fof(f2870,plain,
    ( ! [X0,X1] :
        ( k4_binop_1(sK0,sK6,X0,X1) = k1_binop_1(sK6,X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f2869,f1378])).

fof(f1378,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl10_100 ),
    inference(backward_demodulation,[],[f1375,f94])).

fof(f94,plain,(
    v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f1375,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relat_1(sK6)
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1372,f95])).

fof(f95,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f80])).

fof(f1372,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl10_100 ),
    inference(superposition,[],[f1077,f115])).

fof(f1077,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6)
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f2869,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | k4_binop_1(sK0,sK6,X0,X1) = k1_binop_1(sK6,X0,X1) )
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f2868,f1375])).

fof(f2868,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
        | k4_binop_1(sK0,sK6,X0,X1) = k1_binop_1(sK6,X0,X1) )
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f2866,f1379])).

fof(f1379,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ spl10_100 ),
    inference(backward_demodulation,[],[f1375,f95])).

fof(f2866,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
        | k4_binop_1(sK0,sK6,X0,X1) = k1_binop_1(sK6,X0,X1) )
    | ~ spl10_100 ),
    inference(superposition,[],[f1546,f1375])).

fof(f1546,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,X6),X6)))
      | ~ m1_subset_1(X7,X6)
      | ~ m1_subset_1(X5,X6)
      | ~ v1_funct_2(sK6,k2_zfmisc_1(X6,X6),X6)
      | k4_binop_1(X6,sK6,X7,X5) = k1_binop_1(sK6,X7,X5) ) ),
    inference(resolution,[],[f132,f93])).

fof(f9252,plain,
    ( k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ spl10_979 ),
    inference(avatar_component_clause,[],[f9251])).

fof(f9281,plain,
    ( ~ spl10_104
    | spl10_977 ),
    inference(avatar_contradiction_clause,[],[f9280])).

fof(f9280,plain,
    ( $false
    | ~ spl10_104
    | ~ spl10_977 ),
    inference(subsumption_resolution,[],[f9279,f91])).

fof(f9279,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | ~ spl10_104
    | ~ spl10_977 ),
    inference(subsumption_resolution,[],[f9277,f92])).

fof(f9277,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,sK1)
    | ~ spl10_104
    | ~ spl10_977 ),
    inference(resolution,[],[f9246,f2602])).

fof(f2602,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_binop_1(sK1,sK7,X0,X1),sK1)
        | ~ m1_subset_1(X1,sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f2601,f1572])).

fof(f2601,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(k4_binop_1(sK1,sK7,X0,X1),sK1) )
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f2600,f1569])).

fof(f2600,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK1)
        | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
        | m1_subset_1(k4_binop_1(sK1,sK7,X0,X1),sK1) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f2598,f1573])).

fof(f2598,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK1)
        | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
        | m1_subset_1(k4_binop_1(sK1,sK7,X0,X1),sK1) )
    | ~ spl10_104 ),
    inference(superposition,[],[f1353,f1569])).

fof(f1353,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X9,X9),X9)))
      | ~ m1_subset_1(X10,X9)
      | ~ m1_subset_1(X8,X9)
      | ~ v1_funct_2(sK7,k2_zfmisc_1(X9,X9),X9)
      | m1_subset_1(k4_binop_1(X9,sK7,X10,X8),X9) ) ),
    inference(resolution,[],[f131,f96])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',dt_k4_binop_1)).

fof(f9246,plain,
    ( ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1)
    | ~ spl10_977 ),
    inference(avatar_component_clause,[],[f9245])).

fof(f9245,plain,
    ( spl10_977
  <=> ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_977])])).

fof(f9258,plain,
    ( ~ spl10_100
    | spl10_975 ),
    inference(avatar_contradiction_clause,[],[f9257])).

fof(f9257,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_975 ),
    inference(subsumption_resolution,[],[f9256,f89])).

fof(f9256,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl10_100
    | ~ spl10_975 ),
    inference(subsumption_resolution,[],[f9254,f90])).

fof(f9254,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl10_100
    | ~ spl10_975 ),
    inference(resolution,[],[f9240,f2379])).

fof(f2379,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_binop_1(sK0,sK6,X2,X3),sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X2,sK0) )
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f2378,f1378])).

fof(f2378,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | m1_subset_1(k4_binop_1(sK0,sK6,X2,X3),sK0) )
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f2377,f1375])).

fof(f2377,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
        | m1_subset_1(k4_binop_1(sK0,sK6,X2,X3),sK0) )
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f2359,f1379])).

fof(f2359,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
        | m1_subset_1(k4_binop_1(sK0,sK6,X2,X3),sK0) )
    | ~ spl10_100 ),
    inference(superposition,[],[f1352,f1375])).

fof(f1352,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,X6),X6)))
      | ~ m1_subset_1(X7,X6)
      | ~ m1_subset_1(X5,X6)
      | ~ v1_funct_2(sK6,k2_zfmisc_1(X6,X6),X6)
      | m1_subset_1(k4_binop_1(X6,sK6,X7,X5),X6) ) ),
    inference(resolution,[],[f131,f93])).

fof(f9240,plain,
    ( ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0)
    | ~ spl10_975 ),
    inference(avatar_component_clause,[],[f9239])).

fof(f9239,plain,
    ( spl10_975
  <=> ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_975])])).

fof(f9253,plain,
    ( ~ spl10_975
    | ~ spl10_977
    | ~ spl10_979
    | spl10_957 ),
    inference(avatar_split_clause,[],[f9234,f9114,f9251,f9245,f9239])).

fof(f9114,plain,
    ( spl10_957
  <=> k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_957])])).

fof(f9234,plain,
    ( k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1)
    | ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0)
    | ~ spl10_957 ),
    inference(subsumption_resolution,[],[f9233,f87])).

fof(f87,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f9233,plain,
    ( k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1)
    | ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0)
    | v1_xboole_0(sK0)
    | ~ spl10_957 ),
    inference(subsumption_resolution,[],[f9228,f88])).

fof(f88,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f9228,plain,
    ( k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1)
    | ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_957 ),
    inference(superposition,[],[f9115,f125])).

fof(f9115,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ spl10_957 ),
    inference(avatar_component_clause,[],[f9114])).

fof(f9156,plain,(
    spl10_953 ),
    inference(avatar_contradiction_clause,[],[f9155])).

fof(f9155,plain,
    ( $false
    | ~ spl10_953 ),
    inference(subsumption_resolution,[],[f9154,f87])).

fof(f9154,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_953 ),
    inference(subsumption_resolution,[],[f9153,f88])).

fof(f9153,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_953 ),
    inference(subsumption_resolution,[],[f9152,f90])).

fof(f9152,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_953 ),
    inference(subsumption_resolution,[],[f9151,f92])).

fof(f9151,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_953 ),
    inference(resolution,[],[f9102,f553])).

fof(f9102,plain,
    ( ~ m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_953 ),
    inference(avatar_component_clause,[],[f9101])).

fof(f9101,plain,
    ( spl10_953
  <=> ~ m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_953])])).

fof(f9122,plain,(
    spl10_949 ),
    inference(avatar_contradiction_clause,[],[f9121])).

fof(f9121,plain,
    ( $false
    | ~ spl10_949 ),
    inference(subsumption_resolution,[],[f9120,f87])).

fof(f9120,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_949 ),
    inference(subsumption_resolution,[],[f9119,f88])).

fof(f9119,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_949 ),
    inference(subsumption_resolution,[],[f9118,f89])).

fof(f9118,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_949 ),
    inference(subsumption_resolution,[],[f9117,f91])).

fof(f9117,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_949 ),
    inference(resolution,[],[f9089,f553])).

fof(f9089,plain,
    ( ~ m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_949 ),
    inference(avatar_component_clause,[],[f9088])).

fof(f9088,plain,
    ( spl10_949
  <=> ~ m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_949])])).

fof(f9116,plain,
    ( ~ spl10_949
    | ~ spl10_953
    | ~ spl10_957
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_590 ),
    inference(avatar_split_clause,[],[f9062,f5936,f1091,f1076,f9114,f9101,f9088])).

fof(f5936,plain,
    ( spl10_590
  <=> ! [X7,X6] :
        ( ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),X7,X6) = k1_binop_1(k3_funct_4(sK6,sK7),X7,X6)
        | ~ m1_subset_1(X7,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_590])])).

fof(f9062,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_590 ),
    inference(superposition,[],[f3086,f5937])).

fof(f5937,plain,
    ( ! [X6,X7] :
        ( k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),X7,X6) = k1_binop_1(k3_funct_4(sK6,sK7),X7,X6)
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X7,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl10_590 ),
    inference(avatar_component_clause,[],[f5936])).

fof(f3086,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3085,f1378])).

fof(f3085,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3084,f1375])).

fof(f3084,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3083,f1379])).

fof(f3083,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3082,f1375])).

fof(f3082,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3081,f1572])).

fof(f3081,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3080,f1569])).

fof(f3080,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3079,f1573])).

fof(f3079,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3078,f1569])).

fof(f3078,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f3077,f93])).

fof(f3077,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f3076,f96])).

fof(f3076,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f3037,f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',redefinition_k6_filter_1)).

fof(f3037,plain,(
    k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f3036,f87])).

fof(f3036,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3035,f88])).

fof(f3035,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3034,f90])).

fof(f3034,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f3023,f92])).

fof(f3023,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f1257,f125])).

fof(f1257,plain,(
    k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f1256,f87])).

fof(f1256,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f1255,f88])).

fof(f1255,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f1254,f89])).

fof(f1254,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f1252,f91])).

fof(f1252,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(sK4,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f99,f125])).

fof(f99,plain,(
    k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f80])).

fof(f8388,plain,
    ( ~ spl10_436
    | ~ spl10_594
    | spl10_663 ),
    inference(avatar_contradiction_clause,[],[f8387])).

fof(f8387,plain,
    ( $false
    | ~ spl10_436
    | ~ spl10_594
    | ~ spl10_663 ),
    inference(subsumption_resolution,[],[f6810,f6813])).

fof(f6810,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_436
    | ~ spl10_594 ),
    inference(subsumption_resolution,[],[f6809,f100])).

fof(f100,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',dt_o_0_0_xboole_0)).

fof(f6809,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_436
    | ~ spl10_594 ),
    inference(duplicate_literal_removal,[],[f6751])).

fof(f6751,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_436
    | ~ spl10_594 ),
    inference(superposition,[],[f107,f6722])).

fof(f6722,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl10_436
    | ~ spl10_594 ),
    inference(forward_demodulation,[],[f4027,f6195])).

fof(f6195,plain,
    ( k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)) = o_0_0_xboole_0
    | ~ spl10_594 ),
    inference(resolution,[],[f5962,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f102,f101])).

fof(f101,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',d2_xboole_0)).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',t6_boole)).

fof(f5962,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ spl10_594 ),
    inference(avatar_component_clause,[],[f5961])).

fof(f5961,plain,
    ( spl10_594
  <=> v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_594])])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',fc10_subset_1)).

fof(f7368,plain,(
    ~ spl10_662 ),
    inference(avatar_contradiction_clause,[],[f7367])).

fof(f7367,plain,
    ( $false
    | ~ spl10_662 ),
    inference(subsumption_resolution,[],[f7366,f87])).

fof(f7366,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_662 ),
    inference(subsumption_resolution,[],[f7358,f88])).

fof(f7358,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_662 ),
    inference(resolution,[],[f6816,f107])).

fof(f6816,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_662 ),
    inference(avatar_component_clause,[],[f6815])).

fof(f6815,plain,
    ( spl10_662
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_662])])).

fof(f7121,plain,
    ( ~ spl10_100
    | ~ spl10_104
    | spl10_557
    | ~ spl10_630 ),
    inference(avatar_contradiction_clause,[],[f7120])).

fof(f7120,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(subsumption_resolution,[],[f7119,f1378])).

fof(f7119,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f7118,f1375])).

fof(f7118,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(subsumption_resolution,[],[f7117,f1379])).

fof(f7117,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f7116,f1375])).

fof(f7116,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(subsumption_resolution,[],[f7115,f1572])).

fof(f7115,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f7114,f1569])).

fof(f7114,plain,
    ( ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(subsumption_resolution,[],[f7113,f1573])).

fof(f7113,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f7112,f1569])).

fof(f7112,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(subsumption_resolution,[],[f7111,f100])).

fof(f7111,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_557
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f7110,f6210])).

fof(f6210,plain,
    ( o_0_0_xboole_0 = k1_relat_1(k3_funct_4(sK6,sK7))
    | ~ spl10_630 ),
    inference(resolution,[],[f6206,f136])).

fof(f6206,plain,
    ( v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ spl10_630 ),
    inference(avatar_component_clause,[],[f6205])).

fof(f6205,plain,
    ( spl10_630
  <=> v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_630])])).

fof(f7110,plain,
    ( ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_557 ),
    inference(subsumption_resolution,[],[f7109,f93])).

fof(f7109,plain,
    ( ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_557 ),
    inference(subsumption_resolution,[],[f7101,f96])).

fof(f7101,plain,
    ( ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_557 ),
    inference(superposition,[],[f5609,f127])).

fof(f5609,plain,
    ( ~ v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
    | ~ spl10_557 ),
    inference(avatar_component_clause,[],[f5608])).

fof(f5608,plain,
    ( spl10_557
  <=> ~ v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_557])])).

fof(f7094,plain,
    ( ~ spl10_417
    | ~ spl10_557
    | spl10_545 ),
    inference(avatar_split_clause,[],[f7086,f5573,f5608,f3957])).

fof(f3957,plain,
    ( spl10_417
  <=> ~ m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_417])])).

fof(f5573,plain,
    ( spl10_545
  <=> ~ v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_545])])).

fof(f7086,plain,
    ( ~ v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_545 ),
    inference(superposition,[],[f5574,f115])).

fof(f5574,plain,
    ( ~ v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7)))
    | ~ spl10_545 ),
    inference(avatar_component_clause,[],[f5573])).

fof(f7048,plain,
    ( ~ spl10_100
    | ~ spl10_104
    | ~ spl10_544
    | spl10_595 ),
    inference(avatar_contradiction_clause,[],[f7047])).

fof(f7047,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_544
    | ~ spl10_595 ),
    inference(subsumption_resolution,[],[f6918,f5959])).

fof(f5959,plain,
    ( ~ v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ spl10_595 ),
    inference(avatar_component_clause,[],[f5958])).

fof(f5958,plain,
    ( spl10_595
  <=> ~ v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_595])])).

fof(f6918,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(subsumption_resolution,[],[f6917,f1378])).

fof(f6917,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(forward_demodulation,[],[f6916,f1375])).

fof(f6916,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(subsumption_resolution,[],[f6915,f1379])).

fof(f6915,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(forward_demodulation,[],[f6914,f1375])).

fof(f6914,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(subsumption_resolution,[],[f6913,f1572])).

fof(f6913,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(forward_demodulation,[],[f6912,f1569])).

fof(f6912,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(subsumption_resolution,[],[f6911,f1573])).

fof(f6911,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_544 ),
    inference(forward_demodulation,[],[f6508,f1569])).

fof(f6508,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_544 ),
    inference(subsumption_resolution,[],[f6507,f93])).

fof(f6507,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_544 ),
    inference(subsumption_resolution,[],[f6505,f96])).

fof(f6505,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_544 ),
    inference(superposition,[],[f5577,f127])).

fof(f5577,plain,
    ( v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7)))
    | ~ spl10_544 ),
    inference(avatar_component_clause,[],[f5576])).

fof(f5576,plain,
    ( spl10_544
  <=> v1_xboole_0(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_544])])).

fof(f6997,plain,
    ( spl10_590
    | spl10_572
    | spl10_574
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f6996,f4008,f1091,f1076,f5686,f5683,f5936])).

fof(f5683,plain,
    ( spl10_572
  <=> ! [X1] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X1,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_572])])).

fof(f5686,plain,
    ( spl10_574
  <=> ! [X0] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(sK7,k2_zfmisc_1(X0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_574])])).

fof(f6996,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(sK7,k2_zfmisc_1(X4,X4),X4)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X5,X5),X5)
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X7,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
        | k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),X7,X6) = k1_binop_1(k3_funct_4(sK6,sK7),X7,X6) )
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_430 ),
    inference(subsumption_resolution,[],[f6995,f3990])).

fof(f3990,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3989,f1378])).

fof(f3989,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3988,f1375])).

fof(f3988,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3987,f1379])).

fof(f3987,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3986,f1375])).

fof(f3986,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3985,f1572])).

fof(f3985,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3984,f1569])).

fof(f3984,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3983,f1573])).

fof(f3983,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3982,f1569])).

fof(f3982,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3981,f93])).

fof(f3981,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3940,f96])).

fof(f3940,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(superposition,[],[f3934,f127])).

fof(f3934,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3933,f93])).

fof(f3933,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(sK6)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3930,f1379])).

fof(f3930,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(sK6)
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(resolution,[],[f3834,f1378])).

fof(f3834,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK6),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
        | v1_funct_2(k6_filter_1(sK0,sK1,X0,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f3831,f1375])).

fof(f3831,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK6),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | v1_funct_2(k6_filter_1(sK0,sK1,X0,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(superposition,[],[f3828,f1375])).

fof(f3828,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | v1_funct_2(k6_filter_1(X0,sK1,X1,sK7),k2_zfmisc_1(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(X0,sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3827,f96])).

fof(f3827,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k6_filter_1(X0,sK1,X1,sK7),k2_zfmisc_1(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(X0,sK1))
        | ~ v1_funct_1(sK7)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f3824,f1573])).

fof(f3824,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
        | v1_funct_2(k6_filter_1(X0,sK1,X1,sK7),k2_zfmisc_1(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(X0,sK1))
        | ~ v1_funct_1(sK7)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1) )
    | ~ spl10_104 ),
    inference(resolution,[],[f2274,f1572])).

fof(f2274,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK7),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
        | v1_funct_2(k6_filter_1(X1,sK1,X2,X0),k2_zfmisc_1(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(X1,sK1)),k2_zfmisc_1(X1,sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X2) )
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f2271,f1569])).

fof(f2271,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK7),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | v1_funct_2(k6_filter_1(X1,sK1,X2,X0),k2_zfmisc_1(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(X1,sK1)),k2_zfmisc_1(X1,sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X2) )
    | ~ spl10_104 ),
    inference(superposition,[],[f129,f1569])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',dt_k6_filter_1)).

fof(f6995,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(sK7,k2_zfmisc_1(X4,X4),X4)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X5,X5),X5)
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X7,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
        | ~ v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
        | k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),X7,X6) = k1_binop_1(k3_funct_4(sK6,sK7),X7,X6) )
    | ~ spl10_430 ),
    inference(subsumption_resolution,[],[f6994,f93])).

fof(f6994,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(sK7,k2_zfmisc_1(X4,X4),X4)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X5,X5),X5)
        | ~ v1_funct_1(sK6)
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X7,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
        | ~ v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
        | k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),X7,X6) = k1_binop_1(k3_funct_4(sK6,sK7),X7,X6) )
    | ~ spl10_430 ),
    inference(subsumption_resolution,[],[f6967,f96])).

fof(f6967,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(sK7,k2_zfmisc_1(X4,X4),X4)
        | ~ v1_funct_1(sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X5,X5),X5)
        | ~ v1_funct_1(sK6)
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X7,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
        | ~ v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
        | k4_binop_1(k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7),X7,X6) = k1_binop_1(k3_funct_4(sK6,sK7),X7,X6) )
    | ~ spl10_430 ),
    inference(resolution,[],[f4009,f3304])).

fof(f3304,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k3_funct_4(X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X5,X5),X5)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X4,X5)
      | ~ m1_subset_1(X6,X5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(k3_funct_4(X2,X0),k2_zfmisc_1(X5,X5),X5)
      | k4_binop_1(X5,k3_funct_4(X2,X0),X6,X4) = k1_binop_1(k3_funct_4(X2,X0),X6,X4) ) ),
    inference(resolution,[],[f2152,f132])).

fof(f2152,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k3_funct_4(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f2150])).

fof(f2150,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k3_funct_4(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f128,f127])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k6_filter_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f6947,plain,
    ( ~ spl10_431
    | spl10_436
    | ~ spl10_100
    | ~ spl10_104
    | spl10_423 ),
    inference(avatar_split_clause,[],[f6946,f3969,f1091,f1076,f4026,f4011])).

fof(f4011,plain,
    ( spl10_431
  <=> ~ m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_431])])).

fof(f3969,plain,
    ( spl10_423
  <=> k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_423])])).

fof(f6946,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))
    | ~ m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_423 ),
    inference(subsumption_resolution,[],[f6939,f3970])).

fof(f3970,plain,
    ( k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0
    | ~ spl10_423 ),
    inference(avatar_component_clause,[],[f3969])).

fof(f6939,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))
    | k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | ~ m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(resolution,[],[f3990,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f117,f101])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',d1_funct_2)).

fof(f6149,plain,
    ( ~ spl10_100
    | ~ spl10_572 ),
    inference(avatar_contradiction_clause,[],[f6148])).

fof(f6148,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_572 ),
    inference(subsumption_resolution,[],[f6147,f1378])).

fof(f6147,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl10_100
    | ~ spl10_572 ),
    inference(forward_demodulation,[],[f6146,f1375])).

fof(f6146,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_572 ),
    inference(subsumption_resolution,[],[f6144,f1379])).

fof(f6144,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_572 ),
    inference(superposition,[],[f5684,f1375])).

fof(f5684,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X1,X1),X1) )
    | ~ spl10_572 ),
    inference(avatar_component_clause,[],[f5683])).

fof(f5826,plain,
    ( ~ spl10_104
    | ~ spl10_574 ),
    inference(avatar_contradiction_clause,[],[f5825])).

fof(f5825,plain,
    ( $false
    | ~ spl10_104
    | ~ spl10_574 ),
    inference(subsumption_resolution,[],[f5824,f1572])).

fof(f5824,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ spl10_104
    | ~ spl10_574 ),
    inference(forward_demodulation,[],[f5823,f1569])).

fof(f5823,plain,
    ( ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl10_104
    | ~ spl10_574 ),
    inference(subsumption_resolution,[],[f5822,f1573])).

fof(f5822,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl10_104
    | ~ spl10_574 ),
    inference(superposition,[],[f5687,f1569])).

fof(f5687,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(sK7,k2_zfmisc_1(X0,X0),X0) )
    | ~ spl10_574 ),
    inference(avatar_component_clause,[],[f5686])).

fof(f5713,plain,
    ( ~ spl10_100
    | spl10_577 ),
    inference(avatar_contradiction_clause,[],[f5710])).

fof(f5710,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_577 ),
    inference(resolution,[],[f5709,f1379])).

fof(f5709,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl10_577 ),
    inference(resolution,[],[f5696,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t22_filter_1.p',cc1_relset_1)).

fof(f5696,plain,
    ( ~ v1_relat_1(sK6)
    | ~ spl10_577 ),
    inference(avatar_component_clause,[],[f5695])).

fof(f5695,plain,
    ( spl10_577
  <=> ~ v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_577])])).

fof(f5708,plain,
    ( ~ spl10_104
    | spl10_579 ),
    inference(avatar_contradiction_clause,[],[f5705])).

fof(f5705,plain,
    ( $false
    | ~ spl10_104
    | ~ spl10_579 ),
    inference(resolution,[],[f5704,f1573])).

fof(f5704,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl10_579 ),
    inference(resolution,[],[f5702,f114])).

fof(f5702,plain,
    ( ~ v1_relat_1(sK7)
    | ~ spl10_579 ),
    inference(avatar_component_clause,[],[f5701])).

fof(f5701,plain,
    ( spl10_579
  <=> ~ v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_579])])).

fof(f5667,plain,
    ( ~ spl10_100
    | ~ spl10_104
    | ~ spl10_416
    | spl10_431 ),
    inference(avatar_contradiction_clause,[],[f5666])).

fof(f5666,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5665,f1378])).

fof(f5665,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(forward_demodulation,[],[f5664,f1375])).

fof(f5664,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5663,f1379])).

fof(f5663,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(forward_demodulation,[],[f5662,f1375])).

fof(f5662,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5661,f1572])).

fof(f5661,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(forward_demodulation,[],[f5660,f1569])).

fof(f5660,plain,
    ( ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5659,f1573])).

fof(f5659,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_104
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(forward_demodulation,[],[f5658,f1569])).

fof(f5658,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5657,f93])).

fof(f5657,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5656,f96])).

fof(f5656,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_416
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f5536,f4012])).

fof(f4012,plain,
    ( ~ m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_431 ),
    inference(avatar_component_clause,[],[f4011])).

fof(f5536,plain,
    ( m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl10_416 ),
    inference(superposition,[],[f3955,f127])).

fof(f3955,plain,
    ( m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_416 ),
    inference(avatar_component_clause,[],[f3954])).

fof(f3954,plain,
    ( spl10_416
  <=> m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_416])])).

fof(f5456,plain,(
    ~ spl10_422 ),
    inference(avatar_contradiction_clause,[],[f5455])).

fof(f5455,plain,
    ( $false
    | ~ spl10_422 ),
    inference(subsumption_resolution,[],[f5454,f87])).

fof(f5454,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_422 ),
    inference(subsumption_resolution,[],[f5453,f88])).

fof(f5453,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_422 ),
    inference(subsumption_resolution,[],[f5415,f100])).

fof(f5415,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl10_422 ),
    inference(superposition,[],[f107,f3973])).

fof(f3973,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl10_422 ),
    inference(avatar_component_clause,[],[f3972])).

fof(f3972,plain,
    ( spl10_422
  <=> k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_422])])).

fof(f5397,plain,
    ( ~ spl10_100
    | ~ spl10_104
    | spl10_417 ),
    inference(avatar_contradiction_clause,[],[f5396])).

fof(f5396,plain,
    ( $false
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_417 ),
    inference(subsumption_resolution,[],[f5395,f1378])).

fof(f5395,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_417 ),
    inference(forward_demodulation,[],[f5394,f1375])).

fof(f5394,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl10_100
    | ~ spl10_104
    | ~ spl10_417 ),
    inference(subsumption_resolution,[],[f5393,f3958])).

fof(f3958,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_417 ),
    inference(avatar_component_clause,[],[f3957])).

fof(f5393,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f5391,f1379])).

fof(f5391,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl10_100
    | ~ spl10_104 ),
    inference(superposition,[],[f5389,f1375])).

fof(f5389,plain,
    ( ! [X13] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13)))
        | ~ v1_funct_2(sK6,k2_zfmisc_1(X13,X13),X13)
        | m1_subset_1(k6_filter_1(X13,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,sK1),k2_zfmisc_1(X13,sK1)),k2_zfmisc_1(X13,sK1)))) )
    | ~ spl10_104 ),
    inference(resolution,[],[f5384,f93])).

fof(f5384,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | m1_subset_1(k6_filter_1(X0,sK1,X1,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(X0,sK1)))) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f5383,f96])).

fof(f5383,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_filter_1(X0,sK1,X1,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(X0,sK1))))
        | ~ v1_funct_1(sK7)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1) )
    | ~ spl10_104 ),
    inference(subsumption_resolution,[],[f5380,f1573])).

fof(f5380,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
        | m1_subset_1(k6_filter_1(X0,sK1,X1,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(X0,sK1))))
        | ~ v1_funct_1(sK7)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1) )
    | ~ spl10_104 ),
    inference(resolution,[],[f2319,f1572])).

fof(f2319,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK7),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
        | m1_subset_1(k6_filter_1(X1,sK1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(X1,sK1)),k2_zfmisc_1(X1,sK1))))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X2) )
    | ~ spl10_104 ),
    inference(forward_demodulation,[],[f2316,f1569])).

fof(f2316,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK7),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | m1_subset_1(k6_filter_1(X1,sK1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(X1,sK1)),k2_zfmisc_1(X1,sK1))))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X2) )
    | ~ spl10_104 ),
    inference(superposition,[],[f130,f1569])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1330,plain,(
    spl10_103 ),
    inference(avatar_contradiction_clause,[],[f1329])).

fof(f1329,plain,
    ( $false
    | ~ spl10_103 ),
    inference(subsumption_resolution,[],[f1086,f98])).

fof(f1086,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_103 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f1085,plain,
    ( spl10_103
  <=> ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f1328,plain,(
    spl10_99 ),
    inference(avatar_contradiction_clause,[],[f1327])).

fof(f1327,plain,
    ( $false
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1071,f95])).

fof(f1071,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl10_99
  <=> ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f1093,plain,
    ( ~ spl10_103
    | spl10_104
    | spl10_33 ),
    inference(avatar_split_clause,[],[f1080,f322,f1091,f1085])).

fof(f322,plain,
    ( spl10_33
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f1080,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f1079,f323])).

fof(f323,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f322])).

fof(f1079,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7)
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(resolution,[],[f97,f142])).

fof(f1078,plain,
    ( ~ spl10_99
    | spl10_100
    | spl10_23 ),
    inference(avatar_split_clause,[],[f1065,f290,f1076,f1070])).

fof(f290,plain,
    ( spl10_23
  <=> o_0_0_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f1065,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f1064,f291])).

fof(f291,plain,
    ( o_0_0_xboole_0 != sK0
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f290])).

fof(f1064,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6)
    | o_0_0_xboole_0 = sK0
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(resolution,[],[f94,f142])).

fof(f834,plain,(
    ~ spl10_32 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f823,f100])).

fof(f823,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_32 ),
    inference(backward_demodulation,[],[f326,f88])).

fof(f326,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl10_32
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f785,plain,(
    ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f770,f100])).

fof(f770,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_22 ),
    inference(backward_demodulation,[],[f294,f87])).

fof(f294,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl10_22
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1432+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  228 (1970 expanded)
%              Number of leaves         :   18 ( 865 expanded)
%              Depth                    :   33
%              Number of atoms          : 1675 (32387 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f75,f203,f209,f242,f267,f279,f326,f344])).

fof(f344,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f342,f35])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
      | ~ r3_binop_1(sK1,sK3,sK5)
      | ~ r3_binop_1(sK0,sK2,sK4) )
    & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
      | ( r3_binop_1(sK1,sK3,sK5)
        & r3_binop_1(sK0,sK2,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,sK1)
    & m1_subset_1(sK2,sK0)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f27,f26,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r3_binop_1(X1,X3,X5)
                              | ~ r3_binop_1(X0,X2,X4) )
                            & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X0,X2,X4) ) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,X1) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(sK0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(sK0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                      & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,sK0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5))
                          | ~ r3_binop_1(X1,X3,X5)
                          | ~ r3_binop_1(sK0,X2,X4) )
                        & ( r3_binop_1(k2_zfmisc_1(sK0,X1),k1_domain_1(sK0,X1,X2,X3),k6_filter_1(sK0,X1,X4,X5))
                          | ( r3_binop_1(X1,X3,X5)
                            & r3_binop_1(sK0,X2,X4) ) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                    & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,X1) )
            & m1_subset_1(X2,sK0) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,X2,X3),k6_filter_1(sK0,sK1,X4,X5))
                        | ~ r3_binop_1(sK1,X3,X5)
                        | ~ r3_binop_1(sK0,X2,X4) )
                      & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,X2,X3),k6_filter_1(sK0,sK1,X4,X5))
                        | ( r3_binop_1(sK1,X3,X5)
                          & r3_binop_1(sK0,X2,X4) ) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                      & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                  & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,sK1) )
          & m1_subset_1(X2,sK0) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,X2,X3),k6_filter_1(sK0,sK1,X4,X5))
                      | ~ r3_binop_1(sK1,X3,X5)
                      | ~ r3_binop_1(sK0,X2,X4) )
                    & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,X2,X3),k6_filter_1(sK0,sK1,X4,X5))
                      | ( r3_binop_1(sK1,X3,X5)
                        & r3_binop_1(sK0,X2,X4) ) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                    & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,sK1) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,X3),k6_filter_1(sK0,sK1,X4,X5))
                    | ~ r3_binop_1(sK1,X3,X5)
                    | ~ r3_binop_1(sK0,sK2,X4) )
                  & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,X3),k6_filter_1(sK0,sK1,X4,X5))
                    | ( r3_binop_1(sK1,X3,X5)
                      & r3_binop_1(sK0,sK2,X4) ) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                  & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
              & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,sK1) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,X3),k6_filter_1(sK0,sK1,X4,X5))
                  | ~ r3_binop_1(sK1,X3,X5)
                  | ~ r3_binop_1(sK0,sK2,X4) )
                & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,X3),k6_filter_1(sK0,sK1,X4,X5))
                  | ( r3_binop_1(sK1,X3,X5)
                    & r3_binop_1(sK0,sK2,X4) ) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
            & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,sK1) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X4,X5))
                | ~ r3_binop_1(sK1,sK3,X5)
                | ~ r3_binop_1(sK0,sK2,X4) )
              & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X4,X5))
                | ( r3_binop_1(sK1,sK3,X5)
                  & r3_binop_1(sK0,sK2,X4) ) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
              & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
          & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X4,X5))
              | ~ r3_binop_1(sK1,sK3,X5)
              | ~ r3_binop_1(sK0,sK2,X4) )
            & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,X4,X5))
              | ( r3_binop_1(sK1,sK3,X5)
                & r3_binop_1(sK0,sK2,X4) ) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
            & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        & v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,X5))
            | ~ r3_binop_1(sK1,sK3,X5)
            | ~ r3_binop_1(sK0,sK2,sK4) )
          & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,X5))
            | ( r3_binop_1(sK1,sK3,X5)
              & r3_binop_1(sK0,sK2,sK4) ) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
          & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      & v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X5] :
        ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,X5))
          | ~ r3_binop_1(sK1,sK3,X5)
          | ~ r3_binop_1(sK0,sK2,sK4) )
        & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,X5))
          | ( r3_binop_1(sK1,sK3,X5)
            & r3_binop_1(sK0,sK2,sK4) ) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
        & v1_funct_1(X5) )
   => ( ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
        | ~ r3_binop_1(sK1,sK3,sK5)
        | ~ r3_binop_1(sK0,sK2,sK4) )
      & ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
        | ( r3_binop_1(sK1,sK3,sK5)
          & r3_binop_1(sK0,sK2,sK4) ) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X1)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                          & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X5) )
                           => ( ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X0,X2,X4) )
                            <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_filter_1)).

fof(f342,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f341,f36])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f341,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f340,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f340,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f339,f38])).

fof(f38,plain,(
    m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f339,plain,
    ( ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f338,f39])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f338,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f337,f40])).

fof(f40,plain,(
    v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f337,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f336,f41])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f336,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f335,f42])).

fof(f42,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f335,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f334,f43])).

fof(f43,plain,(
    v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f334,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f333,f44])).

fof(f44,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f333,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f332,f328])).

fof(f328,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f286,f37])).

fof(f286,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f63,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK4)
      | r2_binop_1(sK0,X0,sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f84,f39])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK4)
      | r2_binop_1(sK0,X0,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK4)
      | r2_binop_1(sK0,X0,sK4)
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f55,f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r3_binop_1(X0,X1,X2)
      | r2_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).

fof(f63,plain,
    ( r3_binop_1(sK0,sK2,sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_1
  <=> r3_binop_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f332,plain,
    ( ~ r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f331,f327])).

fof(f327,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f289,f38])).

fof(f289,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK3,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f67,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r3_binop_1(sK1,X1,sK5)
      | r2_binop_1(sK1,X1,sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,(
    ! [X1] :
      ( ~ r3_binop_1(sK1,X1,sK5)
      | r2_binop_1(sK1,X1,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r3_binop_1(sK1,X1,sK5)
      | r2_binop_1(sK1,X1,sK5)
      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(resolution,[],[f55,f44])).

fof(f67,plain,
    ( r3_binop_1(sK1,sK3,sK5)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_2
  <=> r3_binop_1(sK1,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f331,plain,
    ( ~ r2_binop_1(sK1,sK3,sK5)
    | ~ r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_5 ),
    inference(resolution,[],[f201,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ r2_binop_1(X1,X3,X5)
      | ~ r2_binop_1(X0,X2,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_binop_1(X1,X3,X5)
                                & r2_binop_1(X0,X2,X4) )
                              | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r2_binop_1(X1,X3,X5)
                              | ~ r2_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

% (25028)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_binop_1(X1,X3,X5)
                                & r2_binop_1(X0,X2,X4) )
                              | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r2_binop_1(X1,X3,X5)
                              | ~ r2_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

% (25016)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_filter_1)).

fof(f201,plain,
    ( ~ r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_5
  <=> r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f326,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f324,f35])).

fof(f324,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f323,f36])).

fof(f323,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f322,f37])).

fof(f322,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f321,f38])).

fof(f321,plain,
    ( ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f320,f39])).

fof(f320,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f319,f40])).

fof(f319,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f318,f41])).

fof(f318,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f317,f42])).

fof(f317,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f316,f43])).

fof(f316,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f315,f44])).

fof(f315,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f314,f288])).

fof(f288,plain,
    ( r1_binop_1(sK0,sK2,sK4)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f287,f37])).

fof(f287,plain,
    ( r1_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f63,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK4)
      | r1_binop_1(sK0,X0,sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK4)
      | r1_binop_1(sK0,X0,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r3_binop_1(sK0,X0,sK4)
      | r1_binop_1(sK0,X0,sK4)
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f54,f41])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r3_binop_1(X0,X1,X2)
      | r1_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f314,plain,
    ( ~ r1_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f313,f291])).

fof(f291,plain,
    ( r1_binop_1(sK1,sK3,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f290,f38])).

fof(f290,plain,
    ( r1_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK3,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f67,f81])).

fof(f81,plain,(
    ! [X1] :
      ( ~ r3_binop_1(sK1,X1,sK5)
      | r1_binop_1(sK1,X1,sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f80,plain,(
    ! [X1] :
      ( ~ r3_binop_1(sK1,X1,sK5)
      | r1_binop_1(sK1,X1,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f77,f43])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r3_binop_1(sK1,X1,sK5)
      | r1_binop_1(sK1,X1,sK5)
      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(resolution,[],[f54,f44])).

fof(f313,plain,
    ( ~ r1_binop_1(sK1,sK3,sK5)
    | ~ r1_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f312,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | ~ r1_binop_1(X1,X3,X5)
      | ~ r1_binop_1(X0,X2,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r1_binop_1(X1,X3,X5)
                                & r1_binop_1(X0,X2,X4) )
                              | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r1_binop_1(X1,X3,X5)
                              | ~ r1_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r1_binop_1(X1,X3,X5)
                                & r1_binop_1(X0,X2,X4) )
                              | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                            & ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r1_binop_1(X1,X3,X5)
                              | ~ r1_binop_1(X0,X2,X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_filter_1)).

fof(f312,plain,
    ( ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f311,f197])).

fof(f197,plain,
    ( m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_4
  <=> m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f311,plain,
    ( ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f310,f72])).

fof(f72,plain,
    ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_3
  <=> r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f310,plain,
    ( ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f309,f44])).

fof(f309,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f308,f39])).

fof(f308,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f307,f40])).

fof(f307,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f306,f41])).

fof(f306,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f305,f42])).

fof(f305,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f302,f43])).

fof(f302,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f125,f202])).

fof(f202,plain,
    ( r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f200])).

fof(f125,plain,(
    ! [X14,X17,X15,X18,X16] :
      ( ~ r2_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | ~ v1_funct_2(X14,k2_zfmisc_1(X15,X15),X15)
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X17,X17),X17)))
      | ~ v1_funct_2(X16,k2_zfmisc_1(X17,X17),X17)
      | ~ v1_funct_1(X16)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
      | ~ r1_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | r3_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | ~ m1_subset_1(X18,k2_zfmisc_1(X17,X15)) ) ),
    inference(subsumption_resolution,[],[f124,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_filter_1)).

fof(f124,plain,(
    ! [X14,X17,X15,X18,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
      | ~ v1_funct_2(X14,k2_zfmisc_1(X15,X15),X15)
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X17,X17),X17)))
      | ~ v1_funct_2(X16,k2_zfmisc_1(X17,X17),X17)
      | ~ v1_funct_1(X16)
      | ~ r2_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | ~ r1_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | r3_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | ~ v1_funct_2(k6_filter_1(X17,X15,X16,X14),k2_zfmisc_1(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X17,X15)),k2_zfmisc_1(X17,X15))
      | ~ m1_subset_1(X18,k2_zfmisc_1(X17,X15)) ) ),
    inference(subsumption_resolution,[],[f115,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_funct_1(k6_filter_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

% (25031)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f115,plain,(
    ! [X14,X17,X15,X18,X16] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
      | ~ v1_funct_2(X14,k2_zfmisc_1(X15,X15),X15)
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X17,X17),X17)))
      | ~ v1_funct_2(X16,k2_zfmisc_1(X17,X17),X17)
      | ~ v1_funct_1(X16)
      | ~ r2_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | ~ r1_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | r3_binop_1(k2_zfmisc_1(X17,X15),X18,k6_filter_1(X17,X15,X16,X14))
      | ~ v1_funct_2(k6_filter_1(X17,X15,X16,X14),k2_zfmisc_1(k2_zfmisc_1(X17,X15),k2_zfmisc_1(X17,X15)),k2_zfmisc_1(X17,X15))
      | ~ v1_funct_1(k6_filter_1(X17,X15,X16,X14))
      | ~ m1_subset_1(X18,k2_zfmisc_1(X17,X15)) ) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | r3_binop_1(X0,X1,X2)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f279,plain,
    ( spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f277,f35])).

fof(f277,plain,
    ( v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f276,f36])).

fof(f276,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f275,f37])).

fof(f275,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f274,f38])).

fof(f274,plain,
    ( ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f273,f39])).

fof(f273,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f272,f40])).

fof(f272,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f271,f41])).

fof(f271,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f270,f42])).

fof(f270,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f269,f43])).

fof(f269,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f268,f44])).

fof(f268,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f255,f245])).

fof(f245,plain,
    ( ~ r1_binop_1(sK0,sK2,sK4)
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f244,f37])).

fof(f244,plain,
    ( ~ r1_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,sK0)
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f243,f64])).

fof(f64,plain,
    ( ~ r3_binop_1(sK0,sK2,sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f243,plain,
    ( ~ r1_binop_1(sK0,sK2,sK4)
    | r3_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f235,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_binop_1(sK0,X0,sK4)
      | ~ r1_binop_1(sK0,X0,sK4)
      | r3_binop_1(sK0,X0,sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f90,f39])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_binop_1(sK0,X0,sK4)
      | ~ r1_binop_1(sK0,X0,sK4)
      | r3_binop_1(sK0,X0,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_binop_1(sK0,X0,sK4)
      | ~ r1_binop_1(sK0,X0,sK4)
      | r3_binop_1(sK0,X0,sK4)
      | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f56,f41])).

fof(f235,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f234,f35])).

fof(f234,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f233,f36])).

fof(f233,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f232,f37])).

% (25034)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
fof(f232,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f231,f38])).

fof(f231,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f230,f39])).

fof(f230,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f229,f40])).

fof(f229,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f228,f41])).

fof(f228,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f227,f42])).

fof(f227,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f226,f43])).

fof(f226,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f215,f44])).

fof(f215,plain,
    ( r2_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f202,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | r2_binop_1(X0,X2,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f255,plain,
    ( r1_binop_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f253,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | r1_binop_1(X0,X2,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f253,plain,
    ( r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f252,f197])).

fof(f252,plain,
    ( r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f251,f44])).

fof(f251,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f250,f39])).

fof(f250,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f249,f40])).

fof(f249,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f248,f41])).

fof(f248,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f247,f42])).

fof(f247,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f246,f43])).

fof(f246,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r1_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f129,f71])).

fof(f71,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f129,plain,(
    ! [X28,X26,X24,X27,X25] :
      ( ~ r3_binop_1(k2_zfmisc_1(X27,X25),X28,k6_filter_1(X27,X25,X26,X24))
      | ~ v1_funct_2(X24,k2_zfmisc_1(X25,X25),X25)
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X27,X27),X27)))
      | ~ v1_funct_2(X26,k2_zfmisc_1(X27,X27),X27)
      | ~ v1_funct_1(X26)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25)))
      | r1_binop_1(k2_zfmisc_1(X27,X25),X28,k6_filter_1(X27,X25,X26,X24))
      | ~ m1_subset_1(X28,k2_zfmisc_1(X27,X25)) ) ),
    inference(subsumption_resolution,[],[f128,f59])).

fof(f128,plain,(
    ! [X28,X26,X24,X27,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25)))
      | ~ v1_funct_2(X24,k2_zfmisc_1(X25,X25),X25)
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X27,X27),X27)))
      | ~ v1_funct_2(X26,k2_zfmisc_1(X27,X27),X27)
      | ~ v1_funct_1(X26)
      | ~ r3_binop_1(k2_zfmisc_1(X27,X25),X28,k6_filter_1(X27,X25,X26,X24))
      | r1_binop_1(k2_zfmisc_1(X27,X25),X28,k6_filter_1(X27,X25,X26,X24))
      | ~ v1_funct_2(k6_filter_1(X27,X25,X26,X24),k2_zfmisc_1(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X27,X25)),k2_zfmisc_1(X27,X25))
      | ~ m1_subset_1(X28,k2_zfmisc_1(X27,X25)) ) ),
    inference(subsumption_resolution,[],[f117,f58])).

fof(f117,plain,(
    ! [X28,X26,X24,X27,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25)))
      | ~ v1_funct_2(X24,k2_zfmisc_1(X25,X25),X25)
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X27,X27),X27)))
      | ~ v1_funct_2(X26,k2_zfmisc_1(X27,X27),X27)
      | ~ v1_funct_1(X26)
      | ~ r3_binop_1(k2_zfmisc_1(X27,X25),X28,k6_filter_1(X27,X25,X26,X24))
      | r1_binop_1(k2_zfmisc_1(X27,X25),X28,k6_filter_1(X27,X25,X26,X24))
      | ~ v1_funct_2(k6_filter_1(X27,X25,X26,X24),k2_zfmisc_1(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X27,X25)),k2_zfmisc_1(X27,X25))
      | ~ v1_funct_1(k6_filter_1(X27,X25,X26,X24))
      | ~ m1_subset_1(X28,k2_zfmisc_1(X27,X25)) ) ),
    inference(resolution,[],[f60,f54])).

fof(f267,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f265,f35])).

fof(f265,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f264,f36])).

fof(f264,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f263,f37])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f262,f38])).

fof(f262,plain,
    ( ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f261,f39])).

fof(f261,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f260,f40])).

fof(f260,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f259,f41])).

fof(f259,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f258,f42])).

% (25025)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
fof(f258,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f257,f43])).

fof(f257,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f256,f44])).

fof(f256,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f254,f241])).

fof(f241,plain,
    ( ~ r1_binop_1(sK1,sK3,sK5)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl6_6
  <=> r1_binop_1(sK1,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f254,plain,
    ( r1_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f253,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | r1_binop_1(X1,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f242,plain,
    ( spl6_2
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f237,f200,f239,f66])).

fof(f237,plain,
    ( ~ r1_binop_1(sK1,sK3,sK5)
    | r3_binop_1(sK1,sK3,sK5)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f236,f38])).

fof(f236,plain,
    ( ~ r1_binop_1(sK1,sK3,sK5)
    | r3_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK3,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f225,f93])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r2_binop_1(sK1,X1,sK5)
      | ~ r1_binop_1(sK1,X1,sK5)
      | r3_binop_1(sK1,X1,sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r2_binop_1(sK1,X1,sK5)
      | ~ r1_binop_1(sK1,X1,sK5)
      | r3_binop_1(sK1,X1,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f89,plain,(
    ! [X1] :
      ( ~ r2_binop_1(sK1,X1,sK5)
      | ~ r1_binop_1(sK1,X1,sK5)
      | r3_binop_1(sK1,X1,sK5)
      | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(resolution,[],[f56,f44])).

fof(f225,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f224,f35])).

fof(f224,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f223,f36])).

fof(f223,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f222,f37])).

fof(f222,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f221,f38])).

fof(f221,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f220,f39])).

fof(f220,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f219,f40])).

fof(f219,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f218,f41])).

fof(f218,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f217,f42])).

fof(f217,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f216,f43])).

fof(f216,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f214,plain,
    ( r2_binop_1(sK1,sK3,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f202,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
      | r2_binop_1(X1,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f209,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f207,f35])).

fof(f207,plain,
    ( v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f206,f36])).

fof(f206,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f205,f37])).

fof(f205,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f204,f38])).

fof(f204,plain,
    ( ~ m1_subset_1(sK3,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_4 ),
    inference(resolution,[],[f198,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_domain_1)).

fof(f198,plain,
    ( ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f196])).

fof(f203,plain,
    ( ~ spl6_4
    | spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f194,f70,f200,f196])).

fof(f194,plain,
    ( r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f193,f44])).

fof(f193,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f192,f39])).

fof(f192,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f191,f40])).

fof(f191,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f190,f41])).

fof(f190,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f189,f42])).

fof(f189,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f188,f43])).

fof(f188,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | r2_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f127,f71])).

fof(f127,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ r3_binop_1(k2_zfmisc_1(X22,X20),X23,k6_filter_1(X22,X20,X21,X19))
      | ~ v1_funct_2(X19,k2_zfmisc_1(X20,X20),X20)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
      | ~ v1_funct_2(X21,k2_zfmisc_1(X22,X22),X22)
      | ~ v1_funct_1(X21)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
      | r2_binop_1(k2_zfmisc_1(X22,X20),X23,k6_filter_1(X22,X20,X21,X19))
      | ~ m1_subset_1(X23,k2_zfmisc_1(X22,X20)) ) ),
    inference(subsumption_resolution,[],[f126,f59])).

% (25023)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
fof(f126,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
      | ~ v1_funct_2(X19,k2_zfmisc_1(X20,X20),X20)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
      | ~ v1_funct_2(X21,k2_zfmisc_1(X22,X22),X22)
      | ~ v1_funct_1(X21)
      | ~ r3_binop_1(k2_zfmisc_1(X22,X20),X23,k6_filter_1(X22,X20,X21,X19))
      | r2_binop_1(k2_zfmisc_1(X22,X20),X23,k6_filter_1(X22,X20,X21,X19))
      | ~ v1_funct_2(k6_filter_1(X22,X20,X21,X19),k2_zfmisc_1(k2_zfmisc_1(X22,X20),k2_zfmisc_1(X22,X20)),k2_zfmisc_1(X22,X20))
      | ~ m1_subset_1(X23,k2_zfmisc_1(X22,X20)) ) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f116,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
      | ~ v1_funct_2(X19,k2_zfmisc_1(X20,X20),X20)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
      | ~ v1_funct_2(X21,k2_zfmisc_1(X22,X22),X22)
      | ~ v1_funct_1(X21)
      | ~ r3_binop_1(k2_zfmisc_1(X22,X20),X23,k6_filter_1(X22,X20,X21,X19))
      | r2_binop_1(k2_zfmisc_1(X22,X20),X23,k6_filter_1(X22,X20,X21,X19))
      | ~ v1_funct_2(k6_filter_1(X22,X20,X21,X19),k2_zfmisc_1(k2_zfmisc_1(X22,X20),k2_zfmisc_1(X22,X20)),k2_zfmisc_1(X22,X20))
      | ~ v1_funct_1(k6_filter_1(X22,X20,X21,X19))
      | ~ m1_subset_1(X23,k2_zfmisc_1(X22,X20)) ) ),
    inference(resolution,[],[f60,f55])).

fof(f75,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f45,f70,f62])).

fof(f45,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f46,f70,f66])).

fof(f46,plain,
    ( r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | r3_binop_1(sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f47,f70,f66,f62])).

fof(f47,plain,
    ( ~ r3_binop_1(k2_zfmisc_1(sK0,sK1),k1_domain_1(sK0,sK1,sK2,sK3),k6_filter_1(sK0,sK1,sK4,sK5))
    | ~ r3_binop_1(sK1,sK3,sK5)
    | ~ r3_binop_1(sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------

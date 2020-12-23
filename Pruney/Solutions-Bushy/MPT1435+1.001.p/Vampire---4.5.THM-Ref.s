%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1435+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:55 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  312 (2589 expanded)
%              Number of leaves         :   21 (1136 expanded)
%              Depth                    :   60
%              Number of atoms          : 2715 (51552 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f897,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f278,f286,f296,f304,f312,f320,f328,f619,f773,f798,f884])).

fof(f884,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f883])).

fof(f883,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f882,f742])).

fof(f742,plain,
    ( r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl6_17
  <=> r4_binop_1(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f882,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f881,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
      | ~ r6_binop_1(sK1,sK4,sK5)
      | ~ r6_binop_1(sK0,sK2,sK3) )
    & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
      | ( r6_binop_1(sK1,sK4,sK5)
        & r6_binop_1(sK0,sK2,sK3) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f24,f23,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r6_binop_1(X1,X4,X5)
                              | ~ r6_binop_1(X0,X2,X3) )
                            & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ( r6_binop_1(X1,X4,X5)
                                & r6_binop_1(X0,X2,X3) ) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X2,X4),k6_filter_1(sK0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(sK0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X2,X4),k6_filter_1(sK0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(sK0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                  & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
              & v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X2,X4),k6_filter_1(sK0,X1,X3,X5))
                          | ~ r6_binop_1(X1,X4,X5)
                          | ~ r6_binop_1(sK0,X2,X3) )
                        & ( r6_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X2,X4),k6_filter_1(sK0,X1,X3,X5))
                          | ( r6_binop_1(X1,X4,X5)
                            & r6_binop_1(sK0,X2,X3) ) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
            & v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X2,X4),k6_filter_1(sK0,sK1,X3,X5))
                        | ~ r6_binop_1(sK1,X4,X5)
                        | ~ r6_binop_1(sK0,X2,X3) )
                      & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X2,X4),k6_filter_1(sK0,sK1,X3,X5))
                        | ( r6_binop_1(sK1,X4,X5)
                          & r6_binop_1(sK0,X2,X3) ) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                      & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                  & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
              & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
          & v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X2,X4),k6_filter_1(sK0,sK1,X3,X5))
                      | ~ r6_binop_1(sK1,X4,X5)
                      | ~ r6_binop_1(sK0,X2,X3) )
                    & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X2,X4),k6_filter_1(sK0,sK1,X3,X5))
                      | ( r6_binop_1(sK1,X4,X5)
                        & r6_binop_1(sK0,X2,X3) ) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                    & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
            & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        & v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,X3,X5))
                    | ~ r6_binop_1(sK1,X4,X5)
                    | ~ r6_binop_1(sK0,sK2,X3) )
                  & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,X3,X5))
                    | ( r6_binop_1(sK1,X4,X5)
                      & r6_binop_1(sK0,sK2,X3) ) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                  & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
              & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
          & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      & v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,X3,X5))
                  | ~ r6_binop_1(sK1,X4,X5)
                  | ~ r6_binop_1(sK0,sK2,X3) )
                & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,X3,X5))
                  | ( r6_binop_1(sK1,X4,X5)
                    & r6_binop_1(sK0,sK2,X3) ) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
            & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,sK3,X5))
                | ~ r6_binop_1(sK1,X4,X5)
                | ~ r6_binop_1(sK0,sK2,sK3) )
              & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,sK3,X5))
                | ( r6_binop_1(sK1,X4,X5)
                  & r6_binop_1(sK0,sK2,sK3) ) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
              & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
          & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      & v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,sK3,X5))
              | ~ r6_binop_1(sK1,X4,X5)
              | ~ r6_binop_1(sK0,sK2,sK3) )
            & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X4),k6_filter_1(sK0,sK1,sK3,X5))
              | ( r6_binop_1(sK1,X4,X5)
                & r6_binop_1(sK0,sK2,sK3) ) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
            & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,X5))
            | ~ r6_binop_1(sK1,sK4,X5)
            | ~ r6_binop_1(sK0,sK2,sK3) )
          & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,X5))
            | ( r6_binop_1(sK1,sK4,X5)
              & r6_binop_1(sK0,sK2,sK3) ) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
          & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      & v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X5] :
        ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,X5))
          | ~ r6_binop_1(sK1,sK4,X5)
          | ~ r6_binop_1(sK0,sK2,sK3) )
        & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,X5))
          | ( r6_binop_1(sK1,sK4,X5)
            & r6_binop_1(sK0,sK2,sK3) ) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
        & v1_funct_1(X5) )
   => ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ~ r6_binop_1(sK1,sK4,sK5)
        | ~ r6_binop_1(sK0,sK2,sK3) )
      & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ( r6_binop_1(sK1,sK4,sK5)
          & r6_binop_1(sK0,sK2,sK3) ) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(X0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(X0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <~> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <~> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X5) )
                           => ( ( r6_binop_1(X1,X4,X5)
                                & r6_binop_1(X0,X2,X3) )
                            <=> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <=> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_filter_1)).

fof(f881,plain,
    ( v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f880,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f880,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f879,f35])).

fof(f35,plain,(
    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f879,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f878,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f878,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f877,f37])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f877,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f876,f38])).

fof(f38,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f876,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f875,f39])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f875,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f874,f40])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f874,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f873,f41])).

fof(f41,plain,(
    v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f873,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f872,f42])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f872,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f871,f43])).

fof(f43,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f871,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f870,f44])).

fof(f44,plain,(
    v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f870,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f869,f45])).

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f869,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f865,f746])).

fof(f746,plain,
    ( r4_binop_1(sK0,sK2,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f745])).

fof(f745,plain,
    ( spl6_18
  <=> r4_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f865,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f842,f179])).

fof(f179,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r4_binop_1(k2_zfmisc_1(sK0,X0),k6_filter_1(sK0,X0,X3,X1),k6_filter_1(sK0,X0,X4,X2))
      | ~ r4_binop_1(sK0,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X0)
      | ~ r4_binop_1(X0,X1,X2) ) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ r4_binop_1(X1,X4,X5)
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r4_binop_1(X1,X4,X5)
                                & r4_binop_1(X0,X2,X3) )
                              | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r4_binop_1(X1,X4,X5)
                              | ~ r4_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r4_binop_1(X1,X4,X5)
                                & r4_binop_1(X0,X2,X3) )
                              | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r4_binop_1(X1,X4,X5)
                              | ~ r4_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_filter_1)).

fof(f842,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f841,f256])).

fof(f256,plain,
    ( v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_3
  <=> v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f841,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f840,f260])).

fof(f260,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl6_4
  <=> v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f840,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f839,f264])).

fof(f264,plain,
    ( m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_5
  <=> m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f839,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f838,f268])).

fof(f268,plain,
    ( v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl6_6
  <=> v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f838,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f837,f272])).

fof(f272,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl6_7
  <=> v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f837,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f836,f276])).

fof(f276,plain,
    ( m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_8
  <=> m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f836,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f807,f67])).

fof(f67,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_2
  <=> r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f807,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | spl6_2 ),
    inference(resolution,[],[f804,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r5_binop_1(X0,X1,X2)
      | r6_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_binop_1)).

fof(f804,plain,
    ( r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f803,f35])).

fof(f803,plain,
    ( r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f802,f36])).

fof(f802,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f801,f34])).

fof(f801,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(resolution,[],[f677,f64])).

fof(f64,plain,
    ( r6_binop_1(sK0,sK2,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_1
  <=> r6_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f677,plain,
    ( ! [X0] :
        ( ~ r6_binop_1(sK0,X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X0,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f676,f37])).

fof(f676,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X0,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ~ r6_binop_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK3) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f675,f38])).

fof(f675,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X0,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ~ r6_binop_1(sK0,X0,sK3)
        | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f671,f39])).

fof(f671,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X0,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ~ r6_binop_1(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3) )
    | spl6_2 ),
    inference(duplicate_literal_removal,[],[f670])).

fof(f670,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X0,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
        | ~ r6_binop_1(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X0) )
    | spl6_2 ),
    inference(resolution,[],[f663,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f663,plain,
    ( ! [X1] :
        ( ~ r5_binop_1(sK0,X1,sK3)
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f662,f37])).

fof(f662,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ r5_binop_1(sK0,X1,sK3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f659,f38])).

fof(f659,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ r5_binop_1(sK0,X1,sK3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | spl6_2 ),
    inference(resolution,[],[f657,f39])).

fof(f657,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5)) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f656,f45])).

fof(f656,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f655,f40])).

fof(f655,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f654,f41])).

fof(f654,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f653,f42])).

fof(f653,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f652,f43])).

fof(f652,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f645,f44])).

fof(f645,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X4)
        | ~ r5_binop_1(sK0,X4,X3)
        | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,sK4),k6_filter_1(sK0,sK1,X3,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) )
    | spl6_2 ),
    inference(resolution,[],[f643,f385])).

fof(f385,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r6_binop_1(sK1,X1,X0)
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(sK0,X3,X2)
      | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X3,X1),k6_filter_1(sK0,sK1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ) ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(sK0,X3,X2)
      | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X3,X1),k6_filter_1(sK0,sK1,X2,X0))
      | ~ r6_binop_1(sK1,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f222,f56])).

fof(f222,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r5_binop_1(sK1,X7,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X6,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
      | ~ v1_funct_2(X7,k2_zfmisc_1(sK1,sK1),sK1)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X4)
      | ~ r5_binop_1(sK0,X4,X5)
      | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X4,X7),k6_filter_1(sK0,sK1,X5,X6)) ) ),
    inference(resolution,[],[f134,f33])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ r5_binop_1(sK0,X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
      | ~ v1_funct_1(X3)
      | ~ r5_binop_1(X0,X1,X2)
      | r5_binop_1(k2_zfmisc_1(sK0,X0),k6_filter_1(sK0,X0,X3,X1),k6_filter_1(sK0,X0,X4,X2)) ) ),
    inference(resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ r5_binop_1(X1,X4,X5)
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r5_binop_1(X1,X4,X5)
                                & r5_binop_1(X0,X2,X3) )
                              | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r5_binop_1(X1,X4,X5)
                              | ~ r5_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r5_binop_1(X1,X4,X5)
                                & r5_binop_1(X0,X2,X3) )
                              | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r5_binop_1(X1,X4,X5)
                              | ~ r5_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_filter_1)).

fof(f643,plain,
    ( r6_binop_1(sK1,sK4,sK5)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f47,f67])).

fof(f47,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f798,plain,
    ( ~ spl6_1
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f796,f34])).

fof(f796,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f795,f35])).

fof(f795,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f794,f36])).

fof(f794,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f793,f37])).

fof(f793,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f792,f38])).

fof(f792,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f791,f39])).

fof(f791,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl6_1
    | spl6_18 ),
    inference(subsumption_resolution,[],[f776,f64])).

fof(f776,plain,
    ( ~ r6_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_18 ),
    inference(resolution,[],[f747,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r4_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f747,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f745])).

fof(f773,plain,
    ( spl6_2
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f772])).

fof(f772,plain,
    ( $false
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f771,f40])).

fof(f771,plain,
    ( ~ v1_funct_1(sK4)
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f770,f41])).

fof(f770,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f769,f42])).

fof(f769,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f768,f43])).

fof(f768,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f767,f44])).

fof(f767,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f766,f45])).

fof(f766,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f751,f643])).

fof(f751,plain,
    ( ~ r6_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | spl6_17 ),
    inference(resolution,[],[f743,f55])).

fof(f743,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f741])).

fof(f619,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f617,f256])).

fof(f617,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f616,f260])).

fof(f616,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f615,f264])).

fof(f615,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f614,f268])).

fof(f614,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f613,f272])).

fof(f613,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f612,f276])).

fof(f612,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f599,f68])).

fof(f68,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f599,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f593,f55])).

fof(f593,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f592,f34])).

fof(f592,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f590,f35])).

fof(f590,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f565,f36])).

fof(f565,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f564,f37])).

fof(f564,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f561,f38])).

fof(f561,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f558,f39])).

fof(f558,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,X1,sK4),k6_filter_1(sK0,sK1,X0,sK5)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f471,f32])).

fof(f471,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f470,f33])).

fof(f470,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f469,f40])).

fof(f469,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f468,f41])).

fof(f468,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f467,f42])).

fof(f467,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f466,f43])).

fof(f466,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f465,f44])).

fof(f465,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f462,f45])).

fof(f462,plain,
    ( ! [X2,X0,X1] :
        ( ~ r4_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X1,sK4),k6_filter_1(X0,sK1,X2,sK5))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X0) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f461,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r4_binop_1(X1,X4,X5)
      | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f461,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f460,f40])).

fof(f460,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f459,f41])).

fof(f459,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f458,f42])).

fof(f458,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f457,f43])).

fof(f457,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f456,f44])).

fof(f456,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f455,f45])).

fof(f455,plain,
    ( ~ r4_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f442,f336])).

fof(f336,plain,
    ( ~ r6_binop_1(sK1,sK4,sK5)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f335,f64])).

fof(f335,plain,
    ( ~ r6_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f48,f68])).

fof(f48,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r6_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f442,plain,
    ( r6_binop_1(sK1,sK4,sK5)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_2 ),
    inference(resolution,[],[f439,f57])).

fof(f439,plain,
    ( r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f438,f32])).

fof(f438,plain,
    ( v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f437,f33])).

fof(f437,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f436,f34])).

fof(f436,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f435,f35])).

fof(f435,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f434,f36])).

fof(f434,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f433,f37])).

fof(f433,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f432,f38])).

fof(f432,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f431,f39])).

fof(f431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f430,f40])).

fof(f430,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f429,f41])).

fof(f429,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f428,f42])).

fof(f428,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f427,f43])).

fof(f427,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f426,f44])).

fof(f426,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f425,f45])).

fof(f425,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ spl6_2 ),
    inference(resolution,[],[f85,f68])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | r5_binop_1(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_filter_1)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X5,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0)) ) ),
    inference(subsumption_resolution,[],[f83,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X5,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0)) ) ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X5,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0)) ) ),
    inference(subsumption_resolution,[],[f81,f60])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X5,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0)) ) ),
    inference(subsumption_resolution,[],[f80,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k6_filter_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X5,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))
      | ~ v1_funct_1(k6_filter_1(X4,X0,X5,X1)) ) ),
    inference(subsumption_resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X0)
      | v1_xboole_0(X4)
      | ~ r6_binop_1(k2_zfmisc_1(X4,X0),k6_filter_1(X4,X0,X5,X1),k6_filter_1(X4,X0,X3,X2))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))
      | ~ v1_funct_1(k6_filter_1(X4,X0,X3,X2))
      | ~ m1_subset_1(k6_filter_1(X4,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))))
      | ~ v1_funct_2(k6_filter_1(X4,X0,X5,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X0),k2_zfmisc_1(X4,X0)),k2_zfmisc_1(X4,X0))
      | ~ v1_funct_1(k6_filter_1(X4,X0,X5,X1)) ) ),
    inference(resolution,[],[f51,f56])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r5_binop_1(X1,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f328,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f326,f37])).

fof(f326,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f325,f38])).

fof(f325,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f324,f39])).

fof(f324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f323,f43])).

fof(f323,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f322,f44])).

fof(f322,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f321,f45])).

fof(f321,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_8 ),
    inference(resolution,[],[f277,f60])).

fof(f277,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f275])).

fof(f320,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f318,f34])).

fof(f318,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f317,f35])).

fof(f317,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f316,f36])).

fof(f316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f315,f40])).

fof(f315,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f314,f41])).

fof(f314,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f313,f42])).

fof(f313,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(resolution,[],[f265,f60])).

fof(f265,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f263])).

fof(f312,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f310,f37])).

fof(f310,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f309,f38])).

fof(f309,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f308,f39])).

fof(f308,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f307,f43])).

fof(f307,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f306,f44])).

fof(f306,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f305,f45])).

fof(f305,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(resolution,[],[f273,f59])).

fof(f273,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f271])).

fof(f304,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f302,f34])).

fof(f302,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f301,f35])).

fof(f301,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f300,f36])).

fof(f300,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f299,f40])).

fof(f299,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f298,f41])).

fof(f298,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f297,f42])).

fof(f297,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(resolution,[],[f261,f59])).

fof(f261,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f259])).

fof(f296,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f294,f37])).

fof(f294,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f293,f38])).

fof(f293,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f292,f39])).

fof(f292,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f291,f43])).

fof(f291,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f290,f44])).

fof(f290,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f289,f45])).

fof(f289,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | spl6_6 ),
    inference(resolution,[],[f269,f58])).

fof(f269,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f267])).

fof(f286,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f284,f34])).

fof(f284,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f283,f35])).

fof(f283,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f282,f36])).

fof(f282,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f281,f40])).

fof(f281,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f280,f41])).

fof(f280,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f279,f42])).

fof(f279,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(resolution,[],[f257,f58])).

fof(f257,plain,
    ( ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f255])).

fof(f278,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f250,f66,f62,f275,f271,f267,f263,f259,f255])).

fof(f250,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f249,f68])).

fof(f249,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f244,f55])).

fof(f244,plain,
    ( ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f243,f40])).

fof(f243,plain,
    ( ~ v1_funct_1(sK4)
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f241,f41])).

fof(f241,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f228,f42])).

fof(f228,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X1),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f227,f43])).

fof(f227,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X1),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f224,f44])).

fof(f224,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(X1)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X1),k6_filter_1(sK0,sK1,sK3,sK5)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f195,f45])).

fof(f195,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(X2,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
        | ~ v1_funct_2(X3,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(X3)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,X3),k6_filter_1(sK0,sK1,sK3,X2)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f125,f33])).

fof(f125,plain,
    ( ! [X4,X5,X3] :
        ( v1_xboole_0(X3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f124,f32])).

fof(f124,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f123,f34])).

fof(f123,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f122,f35])).

fof(f122,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f121,f36])).

fof(f121,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f120,f37])).

fof(f120,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f119,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f110,f39])).

fof(f110,plain,
    ( ! [X4,X5,X3] :
        ( ~ r4_binop_1(k2_zfmisc_1(sK0,X3),k6_filter_1(sK0,X3,sK2,X4),k6_filter_1(sK0,X3,sK3,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(X3)
        | v1_xboole_0(sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f108,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r4_binop_1(X0,X2,X3)
      | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f107,f34])).

fof(f107,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f106,f35])).

fof(f106,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f105,f36])).

fof(f105,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f104,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f103,f38])).

fof(f103,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f102,f39])).

fof(f102,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f101,f63])).

fof(f63,plain,
    ( ~ r6_binop_1(sK0,sK2,sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f101,plain,
    ( r6_binop_1(sK0,sK2,sK3)
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f100,f57])).

fof(f100,plain,
    ( r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,
    ( v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f98,f33])).

fof(f98,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f96,f35])).

fof(f96,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f94,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f92,f39])).

fof(f92,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f91,f40])).

fof(f91,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f90,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f89,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f87,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f86,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f68])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | r5_binop_1(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f77,f59])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X1,X5),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4)) ) ),
    inference(subsumption_resolution,[],[f76,f60])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X1,X5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X1,X5),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4)) ) ),
    inference(subsumption_resolution,[],[f75,f59])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X1,X5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X1,X5),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4)) ) ),
    inference(subsumption_resolution,[],[f74,f60])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X1,X5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X1,X5),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4)) ) ),
    inference(subsumption_resolution,[],[f73,f58])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X1,X5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X1,X5),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))
      | ~ v1_funct_1(k6_filter_1(X0,X4,X1,X5)) ) ),
    inference(subsumption_resolution,[],[f72,f58])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X4)
      | v1_xboole_0(X0)
      | ~ r6_binop_1(k2_zfmisc_1(X0,X4),k6_filter_1(X0,X4,X1,X5),k6_filter_1(X0,X4,X2,X3))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))
      | ~ v1_funct_1(k6_filter_1(X0,X4,X2,X3))
      | ~ m1_subset_1(k6_filter_1(X0,X4,X1,X5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))))
      | ~ v1_funct_2(k6_filter_1(X0,X4,X1,X5),k2_zfmisc_1(k2_zfmisc_1(X0,X4),k2_zfmisc_1(X0,X4)),k2_zfmisc_1(X0,X4))
      | ~ v1_funct_1(k6_filter_1(X0,X4,X1,X5)) ) ),
    inference(resolution,[],[f50,f56])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r5_binop_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f66,f62])).

fof(f46,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------

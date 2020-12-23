%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1673+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  216 (1546 expanded)
%              Number of leaves         :   22 ( 524 expanded)
%              Depth                    :   40
%              Number of atoms          : 1887 (27223 expanded)
%              Number of equality atoms :   97 (3522 expanded)
%              Maximal formula depth    :   23 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f79,f238,f262,f270,f278,f298,f307,f325,f333,f341])).

fof(f341,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f339,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_yellow_0(sK2,sK4)
      | ~ r1_yellow_0(sK2,sK3) )
    & ( r1_yellow_0(sK2,sK4)
      | r1_yellow_0(sK2,sK3) )
    & ! [X3] :
        ( r2_hidden(k1_yellow_0(sK2,X3),sK4)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k1_yellow_0(sK2,sK5(X4)) = X4
          & r1_yellow_0(sK2,sK5(X4))
          & m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
          & v1_finset_1(sK5(X4)) )
        | ~ r2_hidden(X4,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & ! [X6] :
        ( r1_yellow_0(sK2,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_yellow_0(X0,X2)
                  | ~ r1_yellow_0(X0,X1) )
                & ( r1_yellow_0(X0,X2)
                  | r1_yellow_0(X0,X1) )
                & ! [X3] :
                    ( r2_hidden(k1_yellow_0(X0,X3),X2)
                    | k1_xboole_0 = X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X3) )
                & ! [X4] :
                    ( ? [X5] :
                        ( k1_yellow_0(X0,X5) = X4
                        & r1_yellow_0(X0,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(X1))
                        & v1_finset_1(X5) )
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & ! [X6] :
                    ( r1_yellow_0(X0,X6)
                    | k1_xboole_0 = X6
                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X6) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(sK2,X2)
                | ~ r1_yellow_0(sK2,X1) )
              & ( r1_yellow_0(sK2,X2)
                | r1_yellow_0(sK2,X1) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(sK2,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(sK2,X5) = X4
                      & r1_yellow_0(sK2,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
              & ! [X6] :
                  ( r1_yellow_0(sK2,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_yellow_0(sK2,X2)
              | ~ r1_yellow_0(sK2,X1) )
            & ( r1_yellow_0(sK2,X2)
              | r1_yellow_0(sK2,X1) )
            & ! [X3] :
                ( r2_hidden(k1_yellow_0(sK2,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k1_yellow_0(sK2,X5) = X4
                    & r1_yellow_0(sK2,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(X1))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            & ! [X6] :
                ( r1_yellow_0(sK2,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ( ~ r1_yellow_0(sK2,X2)
            | ~ r1_yellow_0(sK2,sK3) )
          & ( r1_yellow_0(sK2,X2)
            | r1_yellow_0(sK2,sK3) )
          & ! [X3] :
              ( r2_hidden(k1_yellow_0(sK2,X3),X2)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
              | ~ v1_finset_1(X3) )
          & ! [X4] :
              ( ? [X5] :
                  ( k1_yellow_0(sK2,X5) = X4
                  & r1_yellow_0(sK2,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(sK3))
                  & v1_finset_1(X5) )
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & ! [X6] :
              ( r1_yellow_0(sK2,X6)
              | k1_xboole_0 = X6
              | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
              | ~ v1_finset_1(X6) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ r1_yellow_0(sK2,X2)
          | ~ r1_yellow_0(sK2,sK3) )
        & ( r1_yellow_0(sK2,X2)
          | r1_yellow_0(sK2,sK3) )
        & ! [X3] :
            ( r2_hidden(k1_yellow_0(sK2,X3),X2)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k1_yellow_0(sK2,X5) = X4
                & r1_yellow_0(sK2,X5)
                & m1_subset_1(X5,k1_zfmisc_1(sK3))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & ! [X6] :
            ( r1_yellow_0(sK2,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ r1_yellow_0(sK2,sK4)
        | ~ r1_yellow_0(sK2,sK3) )
      & ( r1_yellow_0(sK2,sK4)
        | r1_yellow_0(sK2,sK3) )
      & ! [X3] :
          ( r2_hidden(k1_yellow_0(sK2,X3),sK4)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
          | ~ v1_finset_1(X3) )
      & ! [X4] :
          ( ? [X5] :
              ( k1_yellow_0(sK2,X5) = X4
              & r1_yellow_0(sK2,X5)
              & m1_subset_1(X5,k1_zfmisc_1(sK3))
              & v1_finset_1(X5) )
          | ~ r2_hidden(X4,sK4)
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & ! [X6] :
          ( r1_yellow_0(sK2,X6)
          | k1_xboole_0 = X6
          | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
          | ~ v1_finset_1(X6) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X4] :
      ( ? [X5] :
          ( k1_yellow_0(sK2,X5) = X4
          & r1_yellow_0(sK2,X5)
          & m1_subset_1(X5,k1_zfmisc_1(sK3))
          & v1_finset_1(X5) )
     => ( k1_yellow_0(sK2,sK5(X4)) = X4
        & r1_yellow_0(sK2,sK5(X4))
        & m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
        & v1_finset_1(sK5(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(X0,X2)
                | ~ r1_yellow_0(X0,X1) )
              & ( r1_yellow_0(X0,X2)
                | r1_yellow_0(X0,X1) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(X0,X2)
                | ~ r1_yellow_0(X0,X1) )
              & ( r1_yellow_0(X0,X2)
                | r1_yellow_0(X0,X1) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_yellow_0(X0,X1)
              <~> r1_yellow_0(X0,X2) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_yellow_0(X0,X1)
              <~> r1_yellow_0(X0,X2) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ( r1_yellow_0(X0,X1)
                  <=> r1_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => ( r1_yellow_0(X0,X1)
                  <=> r1_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ( r1_yellow_0(X0,X1)
                <=> r1_yellow_0(X0,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_waybel_0)).

% (20554)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f339,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f338,f42])).

fof(f42,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f338,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f337,f317])).

fof(f317,plain,
    ( r2_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f316,f77])).

fof(f77,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl10_1
  <=> r1_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f316,plain,
    ( r2_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r1_yellow_0(sK2,sK3)
    | spl10_2
    | ~ spl10_9 ),
    inference(factoring,[],[f314])).

fof(f314,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK4)) )
    | spl10_2
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f313,f39])).

fof(f313,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | v2_struct_0(sK2) )
    | spl10_2
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f312,f42])).

fof(f312,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_2
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f311,f75])).

fof(f75,plain,
    ( ~ r1_yellow_0(sK2,sK4)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl10_2
  <=> r1_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f311,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | r1_yellow_0(sK2,sK4)
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_9 ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r1_yellow_0(sK2,sK4)
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_9 ),
    inference(resolution,[],[f297,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK9(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK9(X0,X1,X2))
              | r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK9(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK9(X0,X1,X2))
          | r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK2,X0,sK4),u1_struct_0(sK2))
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl10_9
  <=> ! [X0] :
        ( r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ r1_yellow_0(sK2,X0)
        | ~ m1_subset_1(sK9(sK2,X0,sK4),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f337,plain,
    ( ~ r2_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f336,f75])).

fof(f336,plain,
    ( r1_yellow_0(sK2,sK4)
    | ~ r2_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f335,f77])).

fof(f335,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,sK4)
    | ~ r2_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_10 ),
    inference(resolution,[],[f321,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f321,plain,
    ( r2_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl10_10
  <=> r2_lattice3(sK2,sK4,sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f333,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_11 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | spl10_11 ),
    inference(subsumption_resolution,[],[f331,f39])).

fof(f331,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | spl10_11 ),
    inference(subsumption_resolution,[],[f330,f42])).

fof(f330,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | spl10_11 ),
    inference(subsumption_resolution,[],[f329,f75])).

fof(f329,plain,
    ( r1_yellow_0(sK2,sK4)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_11 ),
    inference(subsumption_resolution,[],[f328,f77])).

fof(f328,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,sK4)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_11 ),
    inference(resolution,[],[f324,f67])).

fof(f324,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | spl10_11 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl10_11
  <=> m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f325,plain,
    ( spl10_10
    | ~ spl10_11
    | ~ spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f318,f296,f213,f74,f71,f323,f320])).

fof(f213,plain,
    ( spl10_4
  <=> ! [X0] :
        ( r2_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f318,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | r2_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_9 ),
    inference(resolution,[],[f317,f214])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_lattice3(sK2,sK4,X0) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f307,plain,
    ( spl10_3
    | spl10_3
    | spl10_3 ),
    inference(avatar_split_clause,[],[f306,f210,f210,f210])).

fof(f210,plain,
    ( spl10_3
  <=> ! [X2] :
        ( ~ r2_lattice3(sK2,sK4,X2)
        | r2_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2) ) ),
    inference(subsumption_resolution,[],[f305,f39])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f304,f40])).

fof(f40,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f303,f41])).

fof(f41,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f302,f42])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f301,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f301,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f300,f86])).

fof(f86,plain,(
    ~ sP0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( ~ sP0(sK2,sK3)
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f84,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r1_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f84,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,sK7(X0,sK3))
      | ~ sP0(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3)
      | r1_yellow_0(sK2,sK7(X0,sK3))
      | ~ v1_finset_1(sK7(X0,sK3)) ) ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK7(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3)
      | k1_xboole_0 = sK7(X0,sK3)
      | r1_yellow_0(sK2,sK7(X0,sK3))
      | ~ v1_finset_1(sK7(X0,sK3)) ) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
      | k1_xboole_0 = X6
      | r1_yellow_0(sK2,X6)
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f299,f103])).

fof(f103,plain,(
    ~ sP1(sK4,sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | ~ sP1(sK4,sK2,sK3) ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( ~ r2_hidden(k1_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK4,sK2,X0),k1_zfmisc_1(sK3))
      | ~ sP1(sK4,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK6(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X0] :
      ( ~ sP1(sK4,sK2,X0)
      | ~ m1_subset_1(sK6(sK4,sK2,X0),k1_zfmisc_1(sK3))
      | ~ v1_finset_1(sK6(sK4,sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f90,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK6(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X0] :
      ( ~ sP1(sK4,sK2,X0)
      | k1_xboole_0 = sK6(sK4,sK2,X0)
      | ~ m1_subset_1(sK6(sK4,sK2,X0),k1_zfmisc_1(sK3))
      | ~ v1_finset_1(sK6(sK4,sK2,X0)) ) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK2,X3),sK4)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X1,sK6(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | sP1(sK4,sK2,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f242,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK4,sK2,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK4,sK2,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | sP1(sK4,sK2,sK3)
      | r2_lattice3(sK2,sK3,X2)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f196,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ( ! [X5] :
                    ( k1_yellow_0(X0,X5) != sK8(X0,X1,X2)
                    | ~ r1_yellow_0(X0,X5)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X5) )
                & r2_hidden(sK8(X0,X1,X2),X2)
                & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_yellow_0(X0,X5) != X4
              | ~ r1_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( k1_yellow_0(X0,X5) != sK8(X0,X1,X2)
            | ~ r1_yellow_0(X0,X5)
            | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X5) )
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( ( r2_lattice3(X0,X1,X7)
                      | ~ r2_lattice3(X0,X2,X7) )
                    & ( r2_lattice3(X0,X2,X7)
                      | ~ r2_lattice3(X0,X1,X7) ) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r1_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r1_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                & v1_finset_1(X5) )
                             => ~ ( k1_yellow_0(X0,X5) = X4
                                  & r1_yellow_0(X0,X5) ) )
                          & r2_hidden(X4,X2) ) )
                  & ! [X6] :
                      ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                     => ( k1_xboole_0 != X6
                       => r1_yellow_0(X0,X6) ) ) )
               => ! [X7] :
                    ( m1_subset_1(X7,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X7)
                    <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                    <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X0,sK2,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2) ) ),
    inference(subsumption_resolution,[],[f195,f39])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f194,f40])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f193,f41])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f192,f42])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f191,f43])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f190,f86])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | sP1(X0,sK2,sK3)
      | r2_lattice3(sK2,sK3,X2)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f170,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f169,f43])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f168,f86])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,X1,X0)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,sK3,X0)
      | ~ r2_lattice3(sK2,X1,X0)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f162,f47])).

fof(f47,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_lattice3(sK2,X2,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f136,f48])).

fof(f48,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_hidden(X4,sK4)
      | r1_yellow_0(sK2,sK5(X4)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f46,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_hidden(X4,sK4)
      | v1_finset_1(sK5(X4)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f134,f39])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f133,f40])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X1,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(superposition,[],[f66,f49])).

fof(f49,plain,(
    ! [X4] :
      ( k1_yellow_0(sK2,sK5(X4)) = X4
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_yellow_0(X0,X5) != sK8(X0,X1,X2)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_lattice3(X0,X1,X3)
      | ~ r1_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f298,plain,
    ( spl10_2
    | spl10_9
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f294,f210,f296,f74])).

fof(f294,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | ~ m1_subset_1(sK9(sK2,X0,sK4),u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X0)
        | r1_yellow_0(sK2,sK4)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK4)) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f293,f39])).

fof(f293,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | ~ m1_subset_1(sK9(sK2,X0,sK4),u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X0)
        | r1_yellow_0(sK2,sK4)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | v2_struct_0(sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f225,f42])).

fof(f225,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK3,sK9(sK2,X0,sK4))
        | ~ m1_subset_1(sK9(sK2,X0,sK4),u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X0)
        | r1_yellow_0(sK2,sK4)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK4))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_3 ),
    inference(resolution,[],[f211,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f211,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK2,sK4,X2)
        | r2_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f210])).

fof(f278,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f276,f39])).

fof(f276,plain,
    ( v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f275,f42])).

fof(f275,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f274,f254])).

fof(f254,plain,
    ( r2_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f253,f78])).

fof(f78,plain,
    ( r1_yellow_0(sK2,sK4)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f253,plain,
    ( r2_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ r1_yellow_0(sK2,sK4)
    | spl10_1
    | ~ spl10_4 ),
    inference(factoring,[],[f251])).

fof(f251,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3)) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f250,f39])).

fof(f250,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f249,f42])).

fof(f249,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f248,f72])).

fof(f72,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f248,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | r1_yellow_0(sK2,sK3)
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_4 ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ! [X0] :
        ( r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r1_yellow_0(sK2,sK3)
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f246,f67])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2))
        | r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3)) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f245,f39])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2))
        | r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f244,f42])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2))
        | r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f243,f72])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2))
        | r2_lattice3(sK2,sK4,sK9(sK2,X0,sK3))
        | ~ r1_yellow_0(sK2,X0)
        | r1_yellow_0(sK2,sK3)
        | r2_lattice3(sK2,X0,sK9(sK2,X0,sK3))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_4 ),
    inference(resolution,[],[f214,f68])).

fof(f274,plain,
    ( ~ r2_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f273,f72])).

fof(f273,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f272,f78])).

fof(f272,plain,
    ( ~ r1_yellow_0(sK2,sK4)
    | r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_6 ),
    inference(resolution,[],[f261,f69])).

fof(f261,plain,
    ( r2_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl10_6
  <=> r2_lattice3(sK2,sK3,sK9(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f270,plain,
    ( spl10_1
    | ~ spl10_2
    | spl10_5 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | spl10_5 ),
    inference(subsumption_resolution,[],[f268,f39])).

fof(f268,plain,
    ( v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | spl10_5 ),
    inference(subsumption_resolution,[],[f267,f42])).

fof(f267,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | spl10_5 ),
    inference(subsumption_resolution,[],[f266,f72])).

fof(f266,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_2
    | spl10_5 ),
    inference(subsumption_resolution,[],[f265,f78])).

fof(f265,plain,
    ( ~ r1_yellow_0(sK2,sK4)
    | r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_5 ),
    inference(resolution,[],[f258,f67])).

fof(f258,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | spl10_5 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl10_5
  <=> m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f262,plain,
    ( ~ spl10_5
    | spl10_6
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f255,f213,f210,f74,f71,f260,f257])).

fof(f255,plain,
    ( r2_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(resolution,[],[f254,f211])).

fof(f238,plain,
    ( spl10_4
    | spl10_4
    | spl10_4 ),
    inference(avatar_split_clause,[],[f237,f213,f213,f213])).

fof(f237,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f236,f39])).

fof(f236,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f235,f40])).

fof(f235,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f234,f41])).

fof(f234,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f233,f42])).

fof(f233,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f232,f43])).

fof(f232,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f231,f86])).

fof(f231,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f230,f103])).

fof(f230,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | sP1(sK4,sK2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f228,f44])).

fof(f228,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK4,sK2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X5)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK2,sK4,X3)
      | ~ r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK4,sK2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK4,X4)
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | sP1(sK4,sK2,sK3)
      | r2_lattice3(sK2,sK4,X5)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f186,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f186,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X3,sK2,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5) ) ),
    inference(subsumption_resolution,[],[f185,f39])).

fof(f185,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f184,f40])).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f183,f41])).

fof(f183,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f182,f42])).

fof(f182,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5)
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f181,f43])).

fof(f181,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f173,f86])).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_lattice3(sK2,X3,X5)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X4)
      | ~ r2_lattice3(sK2,sK3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X3),sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | sP1(X3,sK2,sK3)
      | r2_lattice3(sK2,X3,X5)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f166,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,X1,X0)
      | ~ r2_lattice3(sK2,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f165,f43])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,X1,X0)
      | ~ r2_lattice3(sK2,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f164,f86])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,X1,X0)
      | ~ r2_lattice3(sK2,sK3,X0)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X1,sK2,sK3)
      | r2_lattice3(sK2,X1,X0)
      | ~ r2_lattice3(sK2,sK3,X0)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,sK3,X1),sK4)
      | ~ m1_subset_1(sK8(sK2,sK3,X1),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f161,f47])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_lattice3(sK2,X2,X1)
      | ~ r2_lattice3(sK2,X0,X1)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f129,f48])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f128,f46])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f126,f40])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(sK2,X1,X2) != X0
      | ~ r2_lattice3(sK2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sP1(X2,sK2,X1)
      | r2_lattice3(sK2,X2,X3)
      | ~ r1_yellow_0(sK2,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(X1))
      | ~ v1_finset_1(sK5(X0))
      | sP0(sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(superposition,[],[f63,f49])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_yellow_0(X0,X5) != sK8(X0,X1,X2)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_lattice3(X0,X2,X3)
      | ~ r1_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f51,f74,f71])).

fof(f51,plain,
    ( r1_yellow_0(sK2,sK4)
    | r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f52,f74,f71])).

fof(f52,plain,
    ( ~ r1_yellow_0(sK2,sK4)
    | ~ r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------

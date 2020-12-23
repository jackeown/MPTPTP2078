%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t59_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:00 EDT 2019

% Result     : Theorem 11.43s
% Output     : Refutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  439 (2528 expanded)
%              Number of leaves         :   55 (1021 expanded)
%              Depth                    :   30
%              Number of atoms          : 3028 (44113 expanded)
%              Number of equality atoms :  193 (7925 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8890,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1643,f1650,f1660,f2020,f2040,f2067,f3350,f3363,f3371,f3386,f3403,f3947,f6449,f6581,f6588,f6595,f6602,f6761,f6818,f7545,f7719,f7757,f8180,f8326,f8503,f8594,f8602,f8627,f8636,f8637,f8645,f8782,f8786,f8788,f8874,f8888])).

fof(f8888,plain,
    ( ~ spl37_236
    | ~ spl37_284 ),
    inference(avatar_contradiction_clause,[],[f8887])).

fof(f8887,plain,
    ( $false
    | ~ spl37_236
    | ~ spl37_284 ),
    inference(subsumption_resolution,[],[f1627,f7778])).

fof(f7778,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_284 ),
    inference(trivial_inequality_removal,[],[f7776])).

fof(f7776,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | ~ sP0(sK1,sK2)
    | ~ spl37_284 ),
    inference(superposition,[],[f358,f2012])).

fof(f2012,plain,
    ( o_0_0_xboole_0 = sK10(sK1,sK2)
    | ~ spl37_284 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2011,plain,
    ( spl37_284
  <=> o_0_0_xboole_0 = sK10(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_284])])).

fof(f358,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != sK10(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f283,f237])).

fof(f237,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t59_waybel_0.p',d2_xboole_0)).

fof(f283,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK10(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ( ~ r2_yellow_0(X0,sK10(X0,X1))
        & k1_xboole_0 != sK10(X0,X1)
        & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK10(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f181,f182])).

fof(f182,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_yellow_0(X0,sK10(X0,X1))
        & k1_xboole_0 != sK10(X0,X1)
        & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK10(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1627,plain,
    ( sP0(sK1,sK2)
    | ~ spl37_236 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f1626,plain,
    ( spl37_236
  <=> sP0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_236])])).

fof(f8874,plain,
    ( spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(avatar_contradiction_clause,[],[f8873])).

fof(f8873,plain,
    ( $false
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8872,f221])).

fof(f221,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f169])).

fof(f169,plain,
    ( k2_yellow_0(sK1,sK2) != k2_yellow_0(sK1,sK3)
    & r2_yellow_0(sK1,sK2)
    & ! [X3] :
        ( r2_hidden(k2_yellow_0(sK1,X3),sK3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k2_yellow_0(sK1,sK4(X4)) = X4
          & r2_yellow_0(sK1,sK4(X4))
          & m1_subset_1(sK4(X4),k1_zfmisc_1(sK2))
          & v1_finset_1(sK4(X4)) )
        | ~ r2_hidden(X4,sK3)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    & ! [X6] :
        ( r2_yellow_0(sK1,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f88,f168,f167,f166,f165])).

fof(f165,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
                & r2_yellow_0(X0,X1)
                & ! [X3] :
                    ( r2_hidden(k2_yellow_0(X0,X3),X2)
                    | k1_xboole_0 = X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X3) )
                & ! [X4] :
                    ( ? [X5] :
                        ( k2_yellow_0(X0,X5) = X4
                        & r2_yellow_0(X0,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(X1))
                        & v1_finset_1(X5) )
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & ! [X6] :
                    ( r2_yellow_0(X0,X6)
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
              ( k2_yellow_0(sK1,X1) != k2_yellow_0(sK1,X2)
              & r2_yellow_0(sK1,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(sK1,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(sK1,X5) = X4
                      & r2_yellow_0(sK1,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
              & ! [X6] :
                  ( r2_yellow_0(sK1,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f166,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k2_yellow_0(X0,sK2) != k2_yellow_0(X0,X2)
            & r2_yellow_0(X0,sK2)
            & ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k2_yellow_0(X0,X5) = X4
                    & r2_yellow_0(X0,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(sK2))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & ! [X6] :
                ( r2_yellow_0(X0,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( r2_hidden(k2_yellow_0(X0,X3),X2)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X3) )
          & ! [X4] :
              ( ? [X5] :
                  ( k2_yellow_0(X0,X5) = X4
                  & r2_yellow_0(X0,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(X1))
                  & v1_finset_1(X5) )
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X6] :
              ( r2_yellow_0(X0,X6)
              | k1_xboole_0 = X6
              | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X6) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_yellow_0(X0,sK3) != k2_yellow_0(X0,X1)
        & r2_yellow_0(X0,X1)
        & ! [X3] :
            ( r2_hidden(k2_yellow_0(X0,X3),sK3)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k2_yellow_0(X0,X5) = X4
                & r2_yellow_0(X0,X5)
                & m1_subset_1(X5,k1_zfmisc_1(X1))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,sK3)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & ! [X6] :
            ( r2_yellow_0(X0,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f168,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( k2_yellow_0(X0,X5) = X4
          & r2_yellow_0(X0,X5)
          & m1_subset_1(X5,k1_zfmisc_1(X1))
          & v1_finset_1(X5) )
     => ( k2_yellow_0(X0,sK4(X4)) = X4
        & r2_yellow_0(X0,sK4(X4))
        & m1_subset_1(sK4(X4),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r2_yellow_0(X0,X1)
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r2_yellow_0(X0,X1)
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k2_yellow_0(X0,X4) = X3
                                    & r2_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_yellow_0(X0,X3) ) ) )
                 => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_yellow_0(X0,X1)
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t59_waybel_0.p',t59_waybel_0)).

fof(f8872,plain,
    ( v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8871,f224])).

fof(f224,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f169])).

fof(f8871,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8870,f233])).

fof(f233,plain,(
    r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f169])).

fof(f8870,plain,
    ( ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8869,f6472])).

fof(f6472,plain,
    ( r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_712 ),
    inference(avatar_component_clause,[],[f6471])).

fof(f6471,plain,
    ( spl37_712
  <=> r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_712])])).

fof(f8869,plain,
    ( ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8868,f234])).

fof(f234,plain,(
    k2_yellow_0(sK1,sK2) != k2_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f169])).

fof(f8868,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(resolution,[],[f8865,f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK14(X0,X1,X2))
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK14(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK14(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK14(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK14(X0,X1,X2))
              | r1_lattice3(X0,X1,sK14(X0,X1,X2)) )
            & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f192,f193])).

fof(f193,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK14(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK14(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK14(X0,X1,X2))
          | r1_lattice3(X0,X1,sK14(X0,X1,X2)) )
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f192,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f191])).

fof(f191,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t59_waybel_0.p',t49_yellow_0)).

fof(f8865,plain,
    ( r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8858,f6463])).

fof(f6463,plain,
    ( m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_710 ),
    inference(avatar_component_clause,[],[f6462])).

fof(f6462,plain,
    ( spl37_710
  <=> m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_710])])).

fof(f8858,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_712
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(resolution,[],[f8855,f6472])).

fof(f8855,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16) )
    | ~ spl37_237
    | ~ spl37_238
    | ~ spl37_302
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8854,f8778])).

fof(f8778,plain,
    ( sP33(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8777,f8638])).

fof(f8638,plain,
    ( m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | ~ spl37_238 ),
    inference(resolution,[],[f1633,f1587])).

fof(f1587,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f229,f492])).

fof(f492,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK3)
      | m1_subset_1(X12,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f226,f335])).

fof(f335,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f161,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f160])).

fof(f160,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t59_waybel_0.p',t4_subset)).

fof(f226,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f169])).

fof(f229,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK2)) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f1633,plain,
    ( r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | ~ spl37_238 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f1632,plain,
    ( spl37_238
  <=> r2_hidden(sK12(sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_238])])).

fof(f8777,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP33(sK3,sK2,sK1)
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(equality_resolution,[],[f8017])).

fof(f8017,plain,
    ( ! [X10,X11] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X10,X11)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X10))
        | sP33(X11,X10,sK1) )
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8016,f6587])).

fof(f6587,plain,
    ( v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_736 ),
    inference(avatar_component_clause,[],[f6586])).

fof(f6586,plain,
    ( spl37_736
  <=> v1_finset_1(sK4(sK12(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_736])])).

fof(f8016,plain,
    ( ! [X10,X11] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X10,X11)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X10))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP33(X11,X10,sK1) )
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f7997,f6594])).

fof(f6594,plain,
    ( r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_738 ),
    inference(avatar_component_clause,[],[f6593])).

fof(f6593,plain,
    ( spl37_738
  <=> r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_738])])).

fof(f7997,plain,
    ( ! [X10,X11] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X10,X11)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X10))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP33(X11,X10,sK1) )
    | ~ spl37_740 ),
    inference(superposition,[],[f375,f6601])).

fof(f6601,plain,
    ( k2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) = sK12(sK1,sK2,sK3)
    | ~ spl37_740 ),
    inference(avatar_component_clause,[],[f6600])).

fof(f6600,plain,
    ( spl37_740
  <=> k2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) = sK12(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_740])])).

fof(f375,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP33(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f375_D])).

fof(f375_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP33(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP33])])).

fof(f8854,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8853,f221])).

fof(f8853,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8852,f222])).

fof(f222,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f169])).

fof(f8852,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8851,f223])).

fof(f223,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f169])).

fof(f8851,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8850,f224])).

fof(f8850,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8849,f225])).

fof(f225,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f169])).

fof(f8849,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8848,f226])).

fof(f8848,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8842,f1624])).

fof(f1624,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_237 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f1623,plain,
    ( spl37_237
  <=> ~ sP0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_237])])).

fof(f8842,plain,
    ( ! [X16] :
        ( ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_302 ),
    inference(trivial_inequality_removal,[],[f8840])).

fof(f8840,plain,
    ( ! [X16] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r1_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X16)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_302 ),
    inference(superposition,[],[f376,f2130])).

fof(f2130,plain,
    ( o_0_0_xboole_0 = sK11(sK1,sK2,sK3)
    | ~ spl37_302 ),
    inference(avatar_component_clause,[],[f2129])).

fof(f2129,plain,
    ( spl37_302
  <=> o_0_0_xboole_0 = sK11(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_302])])).

fof(f376,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP33(X2,X1,X0) ) ),
    inference(general_splitting,[],[f362,f375_D])).

fof(f362,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | o_0_0_xboole_0 != sK11(X0,X1,X2)
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f293,f237])).

fof(f293,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 != sK11(X0,X1,X2)
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ( ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
                & k1_xboole_0 != sK11(X0,X1,X2)
                & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
                & v1_finset_1(sK11(X0,X1,X2)) )
              | ( ! [X6] :
                    ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
                    | ~ r2_yellow_0(X0,X6)
                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X6) )
                & r2_hidden(sK12(X0,X1,X2),X2)
                & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f185,f187,f186])).

fof(f186,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_yellow_0(X0,X4),X2)
          & k1_xboole_0 != X4
          & m1_subset_1(X4,k1_zfmisc_1(X1))
          & v1_finset_1(X4) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
        & k1_xboole_0 != sK11(X0,X1,X2)
        & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
        & v1_finset_1(sK11(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f187,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( k2_yellow_0(X0,X6) != X5
              | ~ r2_yellow_0(X0,X6)
              | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X6) )
          & r2_hidden(X5,X2)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
            | ~ r2_yellow_0(X0,X6)
            | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X6) )
        & r2_hidden(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f185,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ? [X4] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X4),X2)
                  & k1_xboole_0 != X4
                  & m1_subset_1(X4,k1_zfmisc_1(X1))
                  & v1_finset_1(X4) )
              | ? [X5] :
                  ( ! [X6] :
                      ( k2_yellow_0(X0,X6) != X5
                      | ~ r2_yellow_0(X0,X6)
                      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X6) )
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f184])).

fof(f184,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( ( r1_lattice3(X0,X1,X7)
                      | ~ r1_lattice3(X0,X2,X7) )
                    & ( r1_lattice3(X0,X2,X7)
                      | ~ r1_lattice3(X0,X1,X7) ) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
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
    inference(nnf_transformation,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
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
    inference(definition_folding,[],[f136,f163])).

fof(f136,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,plain,(
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
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                & v1_finset_1(X5) )
                             => ~ ( k2_yellow_0(X0,X5) = X4
                                  & r2_yellow_0(X0,X5) ) )
                          & r2_hidden(X4,X2) ) )
                  & ! [X6] :
                      ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                     => ( k1_xboole_0 != X6
                       => r2_yellow_0(X0,X6) ) ) )
               => ! [X7] :
                    ( m1_subset_1(X7,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X7)
                    <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,axiom,(
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
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                    <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t59_waybel_0.p',t57_waybel_0)).

fof(f8788,plain,
    ( ~ spl37_299
    | spl37_302
    | ~ spl37_240
    | spl37_301 ),
    inference(avatar_split_clause,[],[f8787,f2120,f1638,f2129,f2117])).

fof(f2117,plain,
    ( spl37_299
  <=> ~ v1_finset_1(sK11(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_299])])).

fof(f1638,plain,
    ( spl37_240
  <=> m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_240])])).

fof(f2120,plain,
    ( spl37_301
  <=> ~ r2_hidden(k2_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_301])])).

fof(f8787,plain,
    ( o_0_0_xboole_0 = sK11(sK1,sK2,sK3)
    | ~ v1_finset_1(sK11(sK1,sK2,sK3))
    | ~ spl37_240
    | ~ spl37_301 ),
    inference(subsumption_resolution,[],[f8657,f2121])).

fof(f2121,plain,
    ( ~ r2_hidden(k2_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3)
    | ~ spl37_301 ),
    inference(avatar_component_clause,[],[f2120])).

fof(f8657,plain,
    ( o_0_0_xboole_0 = sK11(sK1,sK2,sK3)
    | r2_hidden(k2_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3)
    | ~ v1_finset_1(sK11(sK1,sK2,sK3))
    | ~ spl37_240 ),
    inference(resolution,[],[f1639,f354])).

fof(f354,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
      | o_0_0_xboole_0 = X3
      | r2_hidden(k2_yellow_0(sK1,X3),sK3)
      | ~ v1_finset_1(X3) ) ),
    inference(definition_unfolding,[],[f232,f237])).

fof(f232,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK1,X3),sK3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f1639,plain,
    ( m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl37_240 ),
    inference(avatar_component_clause,[],[f1638])).

fof(f8786,plain,
    ( ~ spl37_238
    | spl37_439
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(avatar_contradiction_clause,[],[f8785])).

fof(f8785,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_439
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8784,f3349])).

fof(f3349,plain,
    ( ~ sP35(sK3,sK2,sK1)
    | ~ spl37_439 ),
    inference(avatar_component_clause,[],[f3348])).

fof(f3348,plain,
    ( spl37_439
  <=> ~ sP35(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_439])])).

fof(f8784,plain,
    ( sP35(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8783,f8638])).

fof(f8783,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP35(sK3,sK2,sK1)
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(equality_resolution,[],[f8021])).

fof(f8021,plain,
    ( ! [X14,X15] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X14,X15)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X14))
        | sP35(X15,X14,sK1) )
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8020,f6587])).

fof(f8020,plain,
    ( ! [X14,X15] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X14,X15)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X14))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP35(X15,X14,sK1) )
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f7999,f6594])).

fof(f7999,plain,
    ( ! [X14,X15] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X14,X15)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X14))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP35(X15,X14,sK1) )
    | ~ spl37_740 ),
    inference(superposition,[],[f379,f6601])).

fof(f379,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP35(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f379_D])).

fof(f379_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP35(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP35])])).

fof(f8782,plain,
    ( ~ spl37_238
    | spl37_245
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(avatar_contradiction_clause,[],[f8781])).

fof(f8781,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_245
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8780,f1649])).

fof(f1649,plain,
    ( ~ sP34(sK3,sK2,sK1)
    | ~ spl37_245 ),
    inference(avatar_component_clause,[],[f1648])).

fof(f1648,plain,
    ( spl37_245
  <=> ~ sP34(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_245])])).

fof(f8780,plain,
    ( sP34(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8779,f8638])).

fof(f8779,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP34(sK3,sK2,sK1)
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(equality_resolution,[],[f8019])).

fof(f8019,plain,
    ( ! [X12,X13] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X12,X13)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X12))
        | sP34(X13,X12,sK1) )
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8018,f6587])).

fof(f8018,plain,
    ( ! [X12,X13] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X12,X13)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X12))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP34(X13,X12,sK1) )
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f7998,f6594])).

fof(f7998,plain,
    ( ! [X12,X13] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X12,X13)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X12))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP34(X13,X12,sK1) )
    | ~ spl37_740 ),
    inference(superposition,[],[f377,f6601])).

fof(f377,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP34(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f377_D])).

fof(f377_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP34(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP34])])).

fof(f8645,plain,
    ( ~ spl37_238
    | spl37_869 ),
    inference(avatar_contradiction_clause,[],[f8644])).

fof(f8644,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_869 ),
    inference(subsumption_resolution,[],[f8638,f8635])).

fof(f8635,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | ~ spl37_869 ),
    inference(avatar_component_clause,[],[f8634])).

fof(f8634,plain,
    ( spl37_869
  <=> ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_869])])).

fof(f8637,plain,
    ( spl37_854
    | ~ spl37_869
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(avatar_split_clause,[],[f8491,f6600,f6593,f6586,f8634,f8321])).

fof(f8321,plain,
    ( spl37_854
  <=> sP32(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_854])])).

fof(f8491,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP32(sK3,sK2,sK1)
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(equality_resolution,[],[f8015])).

fof(f8015,plain,
    ( ! [X8,X9] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X8,X9)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X8))
        | sP32(X9,X8,sK1) )
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8014,f6587])).

fof(f8014,plain,
    ( ! [X8,X9] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X8,X9)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X8))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP32(X9,X8,sK1) )
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f7996,f6594])).

fof(f7996,plain,
    ( ! [X8,X9] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X8,X9)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X8))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP32(X9,X8,sK1) )
    | ~ spl37_740 ),
    inference(superposition,[],[f373,f6601])).

fof(f373,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP32(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f373_D])).

fof(f373_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP32(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP32])])).

fof(f8636,plain,
    ( spl37_852
    | ~ spl37_869
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(avatar_split_clause,[],[f8266,f6600,f6593,f6586,f8634,f8260])).

fof(f8260,plain,
    ( spl37_852
  <=> sP29(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_852])])).

fof(f8266,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP29(sK3,sK2,sK1)
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(equality_resolution,[],[f8009])).

fof(f8009,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | sP29(X3,X2,sK1) )
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8008,f6587])).

fof(f8008,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP29(X3,X2,sK1) )
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f7993,f6594])).

fof(f7993,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP29(X3,X2,sK1) )
    | ~ spl37_740 ),
    inference(superposition,[],[f367,f6601])).

fof(f367,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP29(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f367_D])).

fof(f367_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP29(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP29])])).

fof(f8627,plain,
    ( spl37_237
    | spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | spl37_713 ),
    inference(avatar_contradiction_clause,[],[f8626])).

fof(f8626,plain,
    ( $false
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_713 ),
    inference(subsumption_resolution,[],[f8625,f6469])).

fof(f6469,plain,
    ( ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_713 ),
    inference(avatar_component_clause,[],[f6468])).

fof(f6468,plain,
    ( spl37_713
  <=> ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_713])])).

fof(f8625,plain,
    ( r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_713 ),
    inference(subsumption_resolution,[],[f8615,f6463])).

fof(f8615,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_713 ),
    inference(resolution,[],[f8610,f8612])).

fof(f8612,plain,
    ( r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_713 ),
    inference(subsumption_resolution,[],[f8611,f234])).

fof(f8611,plain,
    ( r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ spl37_713 ),
    inference(resolution,[],[f6469,f394])).

fof(f394,plain,(
    ! [X1] :
      ( r1_lattice3(sK1,sK2,sK14(sK1,sK2,X1))
      | r1_lattice3(sK1,X1,sK14(sK1,sK2,X1))
      | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f393,f221])).

fof(f393,plain,(
    ! [X1] :
      ( r1_lattice3(sK1,X1,sK14(sK1,sK2,X1))
      | r1_lattice3(sK1,sK2,sK14(sK1,sK2,X1))
      | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f390,f224])).

fof(f390,plain,(
    ! [X1] :
      ( r1_lattice3(sK1,X1,sK14(sK1,sK2,X1))
      | r1_lattice3(sK1,sK2,sK14(sK1,sK2,X1))
      | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,X1)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f233,f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK14(X0,X1,X2))
      | r1_lattice3(X0,X1,sK14(X0,X1,X2))
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f8610,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8609,f221])).

fof(f8609,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8608,f222])).

fof(f8608,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8607,f223])).

fof(f8607,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8606,f224])).

fof(f8606,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8605,f225])).

fof(f8605,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8604,f226])).

fof(f8604,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8603,f1624])).

fof(f8603,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8567,f1630])).

fof(f1630,plain,
    ( ~ r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | ~ spl37_239 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1629,plain,
    ( spl37_239
  <=> ~ r2_hidden(sK12(sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_239])])).

fof(f8567,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_302 ),
    inference(trivial_inequality_removal,[],[f8552])).

fof(f8552,plain,
    ( ! [X8] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r1_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_302 ),
    inference(superposition,[],[f360,f2130])).

fof(f360,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f304,f237])).

fof(f304,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 != sK11(X0,X1,X2)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f8602,plain,
    ( ~ spl37_853
    | spl37_248
    | spl37_237
    | ~ spl37_302 ),
    inference(avatar_split_clause,[],[f8601,f2129,f1623,f1658,f8263])).

fof(f8263,plain,
    ( spl37_853
  <=> ~ sP29(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_853])])).

fof(f1658,plain,
    ( spl37_248
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK3,X2)
        | r1_lattice3(sK1,sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_248])])).

fof(f8601,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8600,f221])).

fof(f8600,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8599,f222])).

fof(f8599,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8598,f223])).

fof(f8598,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8597,f224])).

fof(f8597,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8596,f225])).

fof(f8596,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8595,f226])).

fof(f8595,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8563,f1624])).

fof(f8563,plain,
    ( ! [X13] :
        ( ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_302 ),
    inference(trivial_inequality_removal,[],[f8557])).

fof(f8557,plain,
    ( ! [X13] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r1_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_302 ),
    inference(superposition,[],[f368,f2130])).

fof(f368,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP29(X2,X1,X0) ) ),
    inference(general_splitting,[],[f359,f367_D])).

fof(f359,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | o_0_0_xboole_0 != sK11(X0,X1,X2)
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f305,f237])).

fof(f305,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 != sK11(X0,X1,X2)
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f8594,plain,
    ( spl37_237
    | spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(avatar_contradiction_clause,[],[f8593])).

fof(f8593,plain,
    ( $false
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f8592,f221])).

fof(f8592,plain,
    ( v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f8591,f224])).

fof(f8591,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f8590,f233])).

fof(f8590,plain,
    ( ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f8589,f6472])).

fof(f8589,plain,
    ( ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f8588,f234])).

fof(f8588,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(resolution,[],[f8585,f314])).

fof(f8585,plain,
    ( r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f8578,f6463])).

fof(f8578,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302
    | ~ spl37_712 ),
    inference(resolution,[],[f8575,f6472])).

fof(f8575,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8574,f221])).

fof(f8574,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8573,f222])).

fof(f8573,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8572,f223])).

fof(f8572,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8571,f224])).

fof(f8571,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8570,f225])).

fof(f8570,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8569,f226])).

fof(f8569,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8568,f1624])).

fof(f8568,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_302 ),
    inference(subsumption_resolution,[],[f8565,f1630])).

fof(f8565,plain,
    ( ! [X10] :
        ( ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_302 ),
    inference(trivial_inequality_removal,[],[f8554])).

fof(f8554,plain,
    ( ! [X10] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r1_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X10)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_302 ),
    inference(superposition,[],[f363,f2130])).

fof(f363,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X2,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f292,f237])).

fof(f292,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 != sK11(X0,X1,X2)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f8503,plain,
    ( spl37_238
    | spl37_242
    | spl37_237
    | ~ spl37_300 ),
    inference(avatar_split_clause,[],[f8502,f2123,f1623,f1641,f1632])).

fof(f1641,plain,
    ( spl37_242
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_lattice3(sK1,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_242])])).

fof(f2123,plain,
    ( spl37_300
  <=> r2_hidden(k2_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_300])])).

fof(f8502,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8501,f221])).

fof(f8501,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8500,f222])).

fof(f8500,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8499,f223])).

fof(f8499,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8498,f224])).

fof(f8498,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8497,f225])).

fof(f8497,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8496,f226])).

fof(f8496,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8302,f1624])).

fof(f8302,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(resolution,[],[f2124,f295])).

fof(f295,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X2,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f2124,plain,
    ( r2_hidden(k2_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3)
    | ~ spl37_300 ),
    inference(avatar_component_clause,[],[f2123])).

fof(f8326,plain,
    ( ~ spl37_855
    | spl37_242
    | spl37_237
    | ~ spl37_300 ),
    inference(avatar_split_clause,[],[f8319,f2123,f1623,f1641,f8324])).

fof(f8324,plain,
    ( spl37_855
  <=> ~ sP32(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_855])])).

fof(f8319,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8318,f221])).

fof(f8318,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8317,f222])).

fof(f8317,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8316,f223])).

fof(f8316,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8315,f224])).

fof(f8315,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8314,f225])).

fof(f8314,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8313,f226])).

fof(f8313,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_237
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f8306,f1624])).

fof(f8306,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(resolution,[],[f2124,f374])).

fof(f374,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP32(X2,X1,X0) ) ),
    inference(general_splitting,[],[f296,f373_D])).

fof(f296,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f8180,plain,
    ( ~ spl37_238
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740
    | spl37_819 ),
    inference(avatar_contradiction_clause,[],[f8179])).

fof(f8179,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740
    | ~ spl37_819 ),
    inference(subsumption_resolution,[],[f8178,f7544])).

fof(f7544,plain,
    ( ~ sP28(sK3,sK2,sK1)
    | ~ spl37_819 ),
    inference(avatar_component_clause,[],[f7543])).

fof(f7543,plain,
    ( spl37_819
  <=> ~ sP28(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_819])])).

fof(f8178,plain,
    ( sP28(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8177,f7788])).

fof(f7788,plain,
    ( m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | ~ spl37_238 ),
    inference(resolution,[],[f1633,f1587])).

fof(f8177,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP28(sK3,sK2,sK1)
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(equality_resolution,[],[f8007])).

fof(f8007,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | sP28(X1,X0,sK1) )
    | ~ spl37_736
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f8006,f6587])).

fof(f8006,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP28(X1,X0,sK1) )
    | ~ spl37_738
    | ~ spl37_740 ),
    inference(subsumption_resolution,[],[f7992,f6594])).

fof(f7992,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP28(X1,X0,sK1) )
    | ~ spl37_740 ),
    inference(superposition,[],[f365,f6601])).

fof(f365,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP28(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f365_D])).

fof(f365_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP28(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP28])])).

fof(f7757,plain,
    ( spl37_236
    | spl37_238
    | spl37_248
    | ~ spl37_300 ),
    inference(avatar_split_clause,[],[f7756,f2123,f1658,f1632,f1626])).

fof(f7756,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7755,f221])).

fof(f7755,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7754,f222])).

fof(f7754,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7753,f223])).

fof(f7753,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7752,f224])).

fof(f7752,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7751,f225])).

fof(f7751,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f6893,f226])).

fof(f6893,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_300 ),
    inference(resolution,[],[f2124,f307])).

fof(f307,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f7719,plain,(
    spl37_711 ),
    inference(avatar_contradiction_clause,[],[f7718])).

fof(f7718,plain,
    ( $false
    | ~ spl37_711 ),
    inference(subsumption_resolution,[],[f7713,f234])).

fof(f7713,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ spl37_711 ),
    inference(resolution,[],[f392,f6466])).

fof(f6466,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_711 ),
    inference(avatar_component_clause,[],[f6465])).

fof(f6465,plain,
    ( spl37_711
  <=> ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_711])])).

fof(f392,plain,(
    ! [X0] :
      ( m1_subset_1(sK14(sK1,sK2,X0),u1_struct_0(sK1))
      | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f391,f221])).

fof(f391,plain,(
    ! [X0] :
      ( m1_subset_1(sK14(sK1,sK2,X0),u1_struct_0(sK1))
      | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f389,f224])).

fof(f389,plain,(
    ! [X0] :
      ( m1_subset_1(sK14(sK1,sK2,X0),u1_struct_0(sK1))
      | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,X0)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f233,f312])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f7545,plain,
    ( ~ spl37_819
    | spl37_236
    | spl37_248
    | ~ spl37_300 ),
    inference(avatar_split_clause,[],[f7538,f2123,f1658,f1626,f7543])).

fof(f7538,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7537,f221])).

fof(f7537,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7536,f222])).

fof(f7536,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7535,f223])).

fof(f7535,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7534,f224])).

fof(f7534,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f7533,f225])).

fof(f7533,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(subsumption_resolution,[],[f6894,f226])).

fof(f6894,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_300 ),
    inference(resolution,[],[f2124,f366])).

fof(f366,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP28(X2,X1,X0) ) ),
    inference(general_splitting,[],[f308,f365_D])).

fof(f308,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k2_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f6818,plain,
    ( ~ spl37_248
    | ~ spl37_710
    | spl37_713 ),
    inference(avatar_contradiction_clause,[],[f6817])).

fof(f6817,plain,
    ( $false
    | ~ spl37_248
    | ~ spl37_710
    | ~ spl37_713 ),
    inference(subsumption_resolution,[],[f6816,f6463])).

fof(f6816,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_248
    | ~ spl37_713 ),
    inference(subsumption_resolution,[],[f6815,f234])).

fof(f6815,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_248
    | ~ spl37_713 ),
    inference(subsumption_resolution,[],[f6810,f6469])).

fof(f6810,plain,
    ( r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_248 ),
    inference(duplicate_literal_removal,[],[f6800])).

fof(f6800,plain,
    ( r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_248 ),
    inference(resolution,[],[f394,f1659])).

fof(f1659,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK1,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X2) )
    | ~ spl37_248 ),
    inference(avatar_component_clause,[],[f1658])).

fof(f6761,plain,
    ( ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(avatar_contradiction_clause,[],[f6760])).

fof(f6760,plain,
    ( $false
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f6679,f234])).

fof(f6679,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f6678,f221])).

fof(f6678,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f6677,f224])).

fof(f6677,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f6676,f233])).

fof(f6676,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f6675,f6472])).

fof(f6675,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK1,sK3)
    | ~ r1_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(resolution,[],[f6668,f314])).

fof(f6668,plain,
    ( r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_242
    | ~ spl37_710
    | ~ spl37_712 ),
    inference(subsumption_resolution,[],[f6661,f6463])).

fof(f6661,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_242
    | ~ spl37_712 ),
    inference(resolution,[],[f1642,f6472])).

fof(f1642,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X0) )
    | ~ spl37_242 ),
    inference(avatar_component_clause,[],[f1641])).

fof(f6602,plain,
    ( spl37_740
    | ~ spl37_239
    | ~ spl37_292 ),
    inference(avatar_split_clause,[],[f4047,f2047,f1629,f6600])).

fof(f2047,plain,
    ( spl37_292
  <=> m1_subset_1(sK12(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_292])])).

fof(f4047,plain,
    ( ~ r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | k2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) = sK12(sK1,sK2,sK3)
    | ~ spl37_292 ),
    inference(resolution,[],[f2048,f231])).

fof(f231,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | k2_yellow_0(sK1,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f169])).

fof(f2048,plain,
    ( m1_subset_1(sK12(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_292 ),
    inference(avatar_component_clause,[],[f2047])).

fof(f6595,plain,
    ( spl37_738
    | ~ spl37_239
    | ~ spl37_292 ),
    inference(avatar_split_clause,[],[f4048,f2047,f1629,f6593])).

fof(f4048,plain,
    ( ~ r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_292 ),
    inference(resolution,[],[f2048,f230])).

fof(f230,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | r2_yellow_0(sK1,sK4(X4)) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f6588,plain,
    ( spl37_736
    | ~ spl37_239
    | ~ spl37_292 ),
    inference(avatar_split_clause,[],[f4049,f2047,f1629,f6586])).

fof(f4049,plain,
    ( ~ r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_292 ),
    inference(resolution,[],[f2048,f228])).

fof(f228,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | v1_finset_1(sK4(X4)) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f6581,plain,
    ( ~ spl37_238
    | ~ spl37_292
    | spl37_441 ),
    inference(avatar_contradiction_clause,[],[f6580])).

fof(f6580,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_292
    | ~ spl37_441 ),
    inference(subsumption_resolution,[],[f6579,f3362])).

fof(f3362,plain,
    ( ~ sP31(sK3,sK2,sK1)
    | ~ spl37_441 ),
    inference(avatar_component_clause,[],[f3361])).

fof(f3361,plain,
    ( spl37_441
  <=> ~ sP31(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_441])])).

fof(f6579,plain,
    ( sP31(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f6578,f4040])).

fof(f4040,plain,
    ( m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | ~ spl37_238 ),
    inference(resolution,[],[f1633,f1587])).

fof(f6578,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP31(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(equality_resolution,[],[f5447])).

fof(f5447,plain,
    ( ! [X6,X7] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X6,X7)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X6))
        | sP31(X7,X6,sK1) )
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f5446,f4053])).

fof(f4053,plain,
    ( v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f4049,f1633])).

fof(f5446,plain,
    ( ! [X6,X7] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X6,X7)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X6))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP31(X7,X6,sK1) )
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f5429,f4052])).

fof(f4052,plain,
    ( r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f4048,f1633])).

fof(f5429,plain,
    ( ! [X6,X7] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X6,X7)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X6))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP31(X7,X6,sK1) )
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(superposition,[],[f371,f4051])).

fof(f4051,plain,
    ( k2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) = sK12(sK1,sK2,sK3)
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f4047,f1633])).

fof(f371,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP31(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f371_D])).

fof(f371_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP31(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP31])])).

fof(f6449,plain,
    ( ~ spl37_238
    | spl37_247
    | ~ spl37_292 ),
    inference(avatar_contradiction_clause,[],[f6448])).

fof(f6448,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_247
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f6447,f1656])).

fof(f1656,plain,
    ( ~ sP30(sK3,sK2,sK1)
    | ~ spl37_247 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f1655,plain,
    ( spl37_247
  <=> ~ sP30(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_247])])).

fof(f6447,plain,
    ( sP30(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f6446,f4040])).

fof(f6446,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP30(sK3,sK2,sK1)
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(equality_resolution,[],[f5445])).

fof(f5445,plain,
    ( ! [X4,X5] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X4,X5)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X4))
        | sP30(X5,X4,sK1) )
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f5444,f4053])).

fof(f5444,plain,
    ( ! [X4,X5] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X4,X5)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X4))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP30(X5,X4,sK1) )
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(subsumption_resolution,[],[f5428,f4052])).

fof(f5428,plain,
    ( ! [X4,X5] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X4,X5)
        | ~ r2_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X4))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP30(X5,X4,sK1) )
    | ~ spl37_238
    | ~ spl37_292 ),
    inference(superposition,[],[f369,f4051])).

fof(f369,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP30(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f369_D])).

fof(f369_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r2_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP30(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP30])])).

fof(f3947,plain,
    ( ~ spl37_236
    | ~ spl37_286 ),
    inference(avatar_contradiction_clause,[],[f3946])).

fof(f3946,plain,
    ( $false
    | ~ spl37_236
    | ~ spl37_286 ),
    inference(subsumption_resolution,[],[f3943,f1627])).

fof(f3943,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_286 ),
    inference(resolution,[],[f2019,f284])).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,sK10(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f2019,plain,
    ( r2_yellow_0(sK1,sK10(sK1,sK2))
    | ~ spl37_286 ),
    inference(avatar_component_clause,[],[f2018])).

fof(f2018,plain,
    ( spl37_286
  <=> r2_yellow_0(sK1,sK10(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_286])])).

fof(f3403,plain,
    ( spl37_236
    | spl37_240
    | spl37_248
    | spl37_239 ),
    inference(avatar_split_clause,[],[f3402,f1629,f1658,f1638,f1626])).

fof(f3402,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
        | sP0(sK1,sK2)
        | r1_lattice3(sK1,sK2,X0)
        | ~ r1_lattice3(sK1,sK3,X0) )
    | ~ spl37_239 ),
    inference(subsumption_resolution,[],[f1774,f1630])).

fof(f1774,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | r2_hidden(sK12(sK1,sK2,sK3),sK3)
      | sP0(sK1,sK2)
      | r1_lattice3(sK1,sK2,X0)
      | ~ r1_lattice3(sK1,sK3,X0) ) ),
    inference(resolution,[],[f510,f225])).

fof(f510,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r1_lattice3(sK1,X7,X6)
      | ~ r1_lattice3(sK1,sK3,X6) ) ),
    inference(subsumption_resolution,[],[f509,f221])).

fof(f509,plain,(
    ! [X6,X7] :
      ( ~ r1_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r1_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f508,f222])).

fof(f508,plain,(
    ! [X6,X7] :
      ( ~ r1_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r1_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f507,f223])).

fof(f507,plain,(
    ! [X6,X7] :
      ( ~ r1_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r1_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f484,f224])).

fof(f484,plain,(
    ! [X6,X7] :
      ( ~ r1_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r1_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f226,f301])).

fof(f301,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f3386,plain,
    ( spl37_236
    | spl37_242
    | spl37_239
    | spl37_299 ),
    inference(avatar_split_clause,[],[f3385,f2117,f1629,f1641,f1626])).

fof(f3385,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3384,f221])).

fof(f3384,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3383,f222])).

fof(f3383,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3382,f223])).

fof(f3382,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3381,f224])).

fof(f3381,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3380,f225])).

fof(f3380,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3379,f226])).

fof(f3379,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f2157,f1630])).

fof(f2157,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_299 ),
    inference(resolution,[],[f2118,f286])).

fof(f286,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X2,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f2118,plain,
    ( ~ v1_finset_1(sK11(sK1,sK2,sK3))
    | ~ spl37_299 ),
    inference(avatar_component_clause,[],[f2117])).

fof(f3371,plain,
    ( spl37_236
    | spl37_248
    | spl37_239
    | spl37_299 ),
    inference(avatar_split_clause,[],[f3370,f2117,f1629,f1658,f1626])).

fof(f3370,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3369,f221])).

fof(f3369,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3368,f222])).

fof(f3368,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3367,f223])).

fof(f3367,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3366,f224])).

fof(f3366,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3365,f225])).

fof(f3365,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3364,f226])).

fof(f3364,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_239
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f2159,f1630])).

fof(f2159,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_299 ),
    inference(resolution,[],[f2118,f298])).

fof(f298,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f3363,plain,
    ( ~ spl37_441
    | spl37_236
    | spl37_248
    | spl37_299 ),
    inference(avatar_split_clause,[],[f3356,f2117,f1658,f1626,f3361])).

fof(f3356,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3355,f221])).

fof(f3355,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3354,f222])).

fof(f3354,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3353,f223])).

fof(f3353,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3352,f224])).

fof(f3352,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3351,f225])).

fof(f3351,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f2160,f226])).

fof(f2160,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(resolution,[],[f2118,f372])).

fof(f372,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP31(X2,X1,X0) ) ),
    inference(general_splitting,[],[f299,f371_D])).

fof(f299,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v1_finset_1(sK11(X0,X1,X2))
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f3350,plain,
    ( ~ spl37_439
    | spl37_236
    | spl37_242
    | spl37_299 ),
    inference(avatar_split_clause,[],[f3343,f2117,f1641,f1626,f3348])).

fof(f3343,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3342,f221])).

fof(f3342,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3341,f222])).

fof(f3341,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3340,f223])).

fof(f3340,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3339,f224])).

fof(f3339,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f3338,f225])).

fof(f3338,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(subsumption_resolution,[],[f2161,f226])).

fof(f2161,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r1_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_299 ),
    inference(resolution,[],[f2118,f380])).

fof(f380,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP35(X2,X1,X0) ) ),
    inference(general_splitting,[],[f287,f379_D])).

fof(f287,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v1_finset_1(sK11(X0,X1,X2))
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f2067,plain,
    ( ~ spl37_238
    | spl37_293 ),
    inference(avatar_contradiction_clause,[],[f2066])).

fof(f2066,plain,
    ( $false
    | ~ spl37_238
    | ~ spl37_293 ),
    inference(subsumption_resolution,[],[f2061,f2045])).

fof(f2045,plain,
    ( ~ m1_subset_1(sK12(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_293 ),
    inference(avatar_component_clause,[],[f2044])).

fof(f2044,plain,
    ( spl37_293
  <=> ~ m1_subset_1(sK12(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_293])])).

fof(f2061,plain,
    ( m1_subset_1(sK12(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_238 ),
    inference(resolution,[],[f1633,f492])).

fof(f2040,plain,
    ( ~ spl37_236
    | spl37_281 ),
    inference(avatar_contradiction_clause,[],[f2039])).

fof(f2039,plain,
    ( $false
    | ~ spl37_236
    | ~ spl37_281 ),
    inference(subsumption_resolution,[],[f2038,f1627])).

fof(f2038,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_281 ),
    inference(resolution,[],[f2000,f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK10(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f2000,plain,
    ( ~ v1_finset_1(sK10(sK1,sK2))
    | ~ spl37_281 ),
    inference(avatar_component_clause,[],[f1999])).

fof(f1999,plain,
    ( spl37_281
  <=> ~ v1_finset_1(sK10(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_281])])).

fof(f2020,plain,
    ( ~ spl37_281
    | spl37_286
    | spl37_284
    | ~ spl37_236 ),
    inference(avatar_split_clause,[],[f1986,f1626,f2011,f2018,f1999])).

fof(f1986,plain,
    ( o_0_0_xboole_0 = sK10(sK1,sK2)
    | r2_yellow_0(sK1,sK10(sK1,sK2))
    | ~ v1_finset_1(sK10(sK1,sK2))
    | ~ spl37_236 ),
    inference(resolution,[],[f1661,f355])).

fof(f355,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
      | o_0_0_xboole_0 = X6
      | r2_yellow_0(sK1,X6)
      | ~ v1_finset_1(X6) ) ),
    inference(definition_unfolding,[],[f227,f237])).

fof(f227,plain,(
    ! [X6] :
      ( r2_yellow_0(sK1,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f1661,plain,
    ( m1_subset_1(sK10(sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl37_236 ),
    inference(resolution,[],[f1627,f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_subset_1(sK10(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f1660,plain,
    ( ~ spl37_247
    | spl37_236
    | spl37_240
    | spl37_248 ),
    inference(avatar_split_clause,[],[f1607,f1658,f1638,f1626,f1655])).

fof(f1607,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | sP0(sK1,sK2)
      | r1_lattice3(sK1,sK2,X2)
      | ~ r1_lattice3(sK1,sK3,X2)
      | ~ sP30(sK3,sK2,sK1) ) ),
    inference(resolution,[],[f225,f514])).

fof(f514,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r1_lattice3(sK1,X9,X8)
      | ~ r1_lattice3(sK1,sK3,X8)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f513,f221])).

fof(f513,plain,(
    ! [X8,X9] :
      ( ~ r1_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r1_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f512,f222])).

fof(f512,plain,(
    ! [X8,X9] :
      ( ~ r1_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r1_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f511,f223])).

fof(f511,plain,(
    ! [X8,X9] :
      ( ~ r1_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r1_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f485,f224])).

fof(f485,plain,(
    ! [X8,X9] :
      ( ~ r1_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r1_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(resolution,[],[f226,f370])).

fof(f370,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | sP0(X0,X1)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP30(X2,X1,X0) ) ),
    inference(general_splitting,[],[f302,f369_D])).

fof(f302,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f1650,plain,
    ( ~ spl37_245
    | spl37_236
    | spl37_240
    | spl37_242 ),
    inference(avatar_split_clause,[],[f1606,f1641,f1638,f1626,f1648])).

fof(f1606,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | sP0(sK1,sK2)
      | r1_lattice3(sK1,sK3,X1)
      | ~ r1_lattice3(sK1,sK2,X1)
      | ~ sP34(sK3,sK2,sK1) ) ),
    inference(resolution,[],[f225,f518])).

fof(f518,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r1_lattice3(sK1,sK3,X11)
      | ~ r1_lattice3(sK1,X10,X11)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f517,f221])).

fof(f517,plain,(
    ! [X10,X11] :
      ( ~ r1_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r1_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f516,f222])).

fof(f516,plain,(
    ! [X10,X11] :
      ( ~ r1_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r1_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f515,f223])).

fof(f515,plain,(
    ! [X10,X11] :
      ( ~ r1_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r1_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f486,f224])).

fof(f486,plain,(
    ! [X10,X11] :
      ( ~ r1_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r1_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(resolution,[],[f226,f378])).

fof(f378,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | sP0(X0,X1)
      | r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP34(X2,X1,X0) ) ),
    inference(general_splitting,[],[f290,f377_D])).

fof(f290,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | k2_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r2_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f1643,plain,
    ( spl37_236
    | spl37_238
    | spl37_240
    | spl37_242 ),
    inference(avatar_split_clause,[],[f1605,f1641,f1638,f1632,f1626])).

fof(f1605,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | r2_hidden(sK12(sK1,sK2,sK3),sK3)
      | sP0(sK1,sK2)
      | r1_lattice3(sK1,sK3,X0)
      | ~ r1_lattice3(sK1,sK2,X0) ) ),
    inference(resolution,[],[f225,f502])).

fof(f502,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r1_lattice3(sK1,sK3,X3)
      | ~ r1_lattice3(sK1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f501,f221])).

fof(f501,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r1_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f500,f222])).

fof(f500,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r1_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f499,f223])).

fof(f499,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r1_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f482,f224])).

fof(f482,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r1_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f226,f289])).

fof(f289,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t53_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:40:59 EDT 2019

% Result     : Theorem 12.38s
% Output     : Refutation 12.38s
% Verified   : 
% Statistics : Number of formulae       :  586 (5601 expanded)
%              Number of leaves         :   55 (1941 expanded)
%              Depth                    :   27
%              Number of atoms          : 4107 (103740 expanded)
%              Number of equality atoms :  165 (13476 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f397,f398,f1774,f20689,f20694,f25888,f25894,f25897,f26052,f26246,f26306,f26342,f26574,f26594,f26644,f26701,f26733,f26761,f26801,f27150,f27226,f27301,f27404,f27670,f27769,f27912,f27996,f28519,f28530,f28590,f28594,f29299,f29303,f29306,f30079,f30084,f30132,f31775,f31798,f31879,f31932,f31944,f32206,f32208,f32415])).

fof(f32415,plain,
    ( spl37_1
    | ~ spl37_2
    | spl37_75
    | ~ spl37_76
    | spl37_201
    | spl37_281
    | ~ spl37_2958 ),
    inference(avatar_contradiction_clause,[],[f32414])).

fof(f32414,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_75
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32413,f981])).

fof(f981,plain,
    ( ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_75 ),
    inference(avatar_component_clause,[],[f980])).

fof(f980,plain,
    ( spl37_75
  <=> ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_75])])).

fof(f32413,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32395,f29869])).

fof(f29869,plain,
    ( m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ spl37_1
    | ~ spl37_2 ),
    inference(resolution,[],[f29865,f390])).

fof(f390,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | ~ spl37_1 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl37_1
  <=> ~ r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_1])])).

fof(f29865,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK1,X0)
        | m1_subset_1(sK14(sK1,sK3,X0),u1_struct_0(sK1)) )
    | ~ spl37_2 ),
    inference(subsumption_resolution,[],[f29864,f223])).

fof(f223,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,
    ( ( ~ r1_yellow_0(sK1,sK3)
      | ~ r1_yellow_0(sK1,sK2) )
    & ( r1_yellow_0(sK1,sK3)
      | r1_yellow_0(sK1,sK2) )
    & ! [X3] :
        ( r2_hidden(k1_yellow_0(sK1,X3),sK3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k1_yellow_0(sK1,sK4(X4)) = X4
          & r1_yellow_0(sK1,sK4(X4))
          & m1_subset_1(sK4(X4),k1_zfmisc_1(sK2))
          & v1_finset_1(sK4(X4)) )
        | ~ r2_hidden(X4,sK3)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    & ! [X6] :
        ( r1_yellow_0(sK1,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f166,f170,f169,f168,f167])).

fof(f167,plain,
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
              ( ( ~ r1_yellow_0(sK1,X2)
                | ~ r1_yellow_0(sK1,X1) )
              & ( r1_yellow_0(sK1,X2)
                | r1_yellow_0(sK1,X1) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(sK1,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(sK1,X5) = X4
                      & r1_yellow_0(sK1,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
              & ! [X6] :
                  ( r1_yellow_0(sK1,X6)
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

fof(f168,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ( ~ r1_yellow_0(X0,X2)
              | ~ r1_yellow_0(X0,sK2) )
            & ( r1_yellow_0(X0,X2)
              | r1_yellow_0(X0,sK2) )
            & ! [X3] :
                ( r2_hidden(k1_yellow_0(X0,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k1_yellow_0(X0,X5) = X4
                    & r1_yellow_0(X0,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(sK2))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & ! [X6] :
                ( r1_yellow_0(X0,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f169,plain,(
    ! [X0,X1] :
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
     => ( ( ~ r1_yellow_0(X0,sK3)
          | ~ r1_yellow_0(X0,X1) )
        & ( r1_yellow_0(X0,sK3)
          | r1_yellow_0(X0,X1) )
        & ! [X3] :
            ( r2_hidden(k1_yellow_0(X0,X3),sK3)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k1_yellow_0(X0,X5) = X4
                & r1_yellow_0(X0,X5)
                & m1_subset_1(X5,k1_zfmisc_1(X1))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,sK3)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & ! [X6] :
            ( r1_yellow_0(X0,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f170,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( k1_yellow_0(X0,X5) = X4
          & r1_yellow_0(X0,X5)
          & m1_subset_1(X5,k1_zfmisc_1(X1))
          & v1_finset_1(X5) )
     => ( k1_yellow_0(X0,sK4(X4)) = X4
        & r1_yellow_0(X0,sK4(X4))
        & m1_subset_1(sK4(X4),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f166,plain,(
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
    inference(flattening,[],[f165])).

fof(f165,plain,(
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
    inference(nnf_transformation,[],[f88])).

fof(f88,plain,(
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
    inference(flattening,[],[f87])).

fof(f87,plain,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t53_waybel_0.p',t53_waybel_0)).

fof(f29864,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK1,X0)
        | m1_subset_1(sK14(sK1,sK3,X0),u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl37_2 ),
    inference(subsumption_resolution,[],[f29862,f226])).

fof(f226,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f171])).

fof(f29862,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK1,X0)
        | m1_subset_1(sK14(sK1,sK3,X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2 ),
    inference(resolution,[],[f393,f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK14(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK14(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK14(X0,X1,X2))
              | r2_lattice3(X0,X1,sK14(X0,X1,X2)) )
            & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f194,f195])).

fof(f195,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK14(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK14(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK14(X0,X1,X2))
          | r2_lattice3(X0,X1,sK14(X0,X1,X2)) )
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
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
    inference(flattening,[],[f193])).

fof(f193,plain,(
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
    inference(nnf_transformation,[],[f140])).

fof(f140,plain,(
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
    inference(flattening,[],[f139])).

fof(f139,plain,(
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
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t53_waybel_0.p',t46_yellow_0)).

fof(f393,plain,
    ( r1_yellow_0(sK1,sK3)
    | ~ spl37_2 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl37_2
  <=> r1_yellow_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2])])).

fof(f32395,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(resolution,[],[f32265,f990])).

fof(f990,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_76 ),
    inference(avatar_component_clause,[],[f989])).

fof(f989,plain,
    ( spl37_76
  <=> r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_76])])).

fof(f32265,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32264,f223])).

fof(f32264,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32263,f224])).

fof(f224,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f171])).

fof(f32263,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32262,f225])).

fof(f225,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f171])).

fof(f32262,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32261,f226])).

fof(f32261,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32260,f227])).

fof(f227,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f171])).

fof(f32260,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32259,f228])).

fof(f228,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f171])).

fof(f32259,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32258,f1466])).

fof(f1466,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_201 ),
    inference(avatar_component_clause,[],[f1465])).

fof(f1465,plain,
    ( spl37_201
  <=> ~ sP0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_201])])).

fof(f32258,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f32244,f1770])).

fof(f1770,plain,
    ( ~ r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | ~ spl37_281 ),
    inference(avatar_component_clause,[],[f1769])).

fof(f1769,plain,
    ( spl37_281
  <=> ~ r2_hidden(sK12(sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_281])])).

fof(f32244,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f297])).

fof(f297,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X2,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ( ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
                & k1_xboole_0 != sK11(X0,X1,X2)
                & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
                & v1_finset_1(sK11(X0,X1,X2)) )
              | ( ! [X6] :
                    ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
                    | ~ r1_yellow_0(X0,X6)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f187,f189,f188])).

fof(f188,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k1_yellow_0(X0,X4),X2)
          & k1_xboole_0 != X4
          & m1_subset_1(X4,k1_zfmisc_1(X1))
          & v1_finset_1(X4) )
     => ( ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
        & k1_xboole_0 != sK11(X0,X1,X2)
        & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
        & v1_finset_1(sK11(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f189,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( k1_yellow_0(X0,X6) != X5
              | ~ r1_yellow_0(X0,X6)
              | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X6) )
          & r2_hidden(X5,X2)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
            | ~ r1_yellow_0(X0,X6)
            | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X6) )
        & r2_hidden(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f187,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ? [X4] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X4),X2)
                  & k1_xboole_0 != X4
                  & m1_subset_1(X4,k1_zfmisc_1(X1))
                  & v1_finset_1(X4) )
              | ? [X5] :
                  ( ! [X6] :
                      ( k1_yellow_0(X0,X6) != X5
                      | ~ r1_yellow_0(X0,X6)
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
    inference(rectify,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( ( r2_lattice3(X0,X1,X7)
                      | ~ r2_lattice3(X0,X2,X7) )
                    & ( r2_lattice3(X0,X2,X7)
                      | ~ r2_lattice3(X0,X1,X7) ) )
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
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f136,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f136,plain,(
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
    inference(flattening,[],[f135])).

fof(f135,plain,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t53_waybel_0.p',t52_waybel_0)).

fof(f25919,plain,
    ( r2_hidden(k1_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3)
    | ~ spl37_2958 ),
    inference(avatar_component_clause,[],[f25918])).

fof(f25918,plain,
    ( spl37_2958
  <=> r2_hidden(k1_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2958])])).

fof(f32208,plain,
    ( ~ spl37_2957
    | spl37_2958
    | spl37_2960
    | ~ spl37_202 ),
    inference(avatar_split_clause,[],[f29991,f1474,f25924,f25918,f25912])).

fof(f25912,plain,
    ( spl37_2957
  <=> ~ v1_finset_1(sK11(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2957])])).

fof(f25924,plain,
    ( spl37_2960
  <=> o_0_0_xboole_0 = sK11(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2960])])).

fof(f1474,plain,
    ( spl37_202
  <=> m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_202])])).

fof(f29991,plain,
    ( o_0_0_xboole_0 = sK11(sK1,sK2,sK3)
    | r2_hidden(k1_yellow_0(sK1,sK11(sK1,sK2,sK3)),sK3)
    | ~ v1_finset_1(sK11(sK1,sK2,sK3))
    | ~ spl37_202 ),
    inference(resolution,[],[f1475,f356])).

fof(f356,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
      | o_0_0_xboole_0 = X3
      | r2_hidden(k1_yellow_0(sK1,X3),sK3)
      | ~ v1_finset_1(X3) ) ),
    inference(definition_unfolding,[],[f234,f239])).

fof(f239,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t53_waybel_0.p',d2_xboole_0)).

fof(f234,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK1,X3),sK3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f1475,plain,
    ( m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl37_202 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f32206,plain,
    ( spl37_1
    | ~ spl37_2
    | spl37_75
    | ~ spl37_76
    | spl37_201
    | spl37_281
    | ~ spl37_2960 ),
    inference(avatar_contradiction_clause,[],[f32205])).

fof(f32205,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_75
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32204,f981])).

fof(f32204,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32191,f29869])).

fof(f32191,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(resolution,[],[f32104,f990])).

fof(f32104,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32103,f223])).

fof(f32103,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32102,f224])).

fof(f32102,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32101,f225])).

fof(f32101,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32100,f226])).

fof(f32100,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32099,f227])).

fof(f32099,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32098,f228])).

fof(f32098,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32097,f1466])).

fof(f32097,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f32094,f1770])).

fof(f32094,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(trivial_inequality_removal,[],[f32083])).

fof(f32083,plain,
    ( ! [X10] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(superposition,[],[f365,f25925])).

fof(f25925,plain,
    ( o_0_0_xboole_0 = sK11(sK1,sK2,sK3)
    | ~ spl37_2960 ),
    inference(avatar_component_clause,[],[f25924])).

fof(f365,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X2,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f294,f239])).

fof(f294,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
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
    inference(cnf_transformation,[],[f190])).

fof(f31944,plain,
    ( spl37_1
    | ~ spl37_2
    | spl37_75
    | ~ spl37_76
    | spl37_201
    | spl37_281
    | spl37_2957 ),
    inference(avatar_contradiction_clause,[],[f31943])).

fof(f31943,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_75
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31942,f981])).

fof(f31942,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31939,f29869])).

fof(f31939,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_76
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(resolution,[],[f990,f31887])).

fof(f31887,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31886,f223])).

fof(f31886,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31885,f224])).

fof(f31885,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31884,f225])).

fof(f31884,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31883,f226])).

fof(f31883,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31882,f227])).

fof(f31882,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31881,f228])).

fof(f31881,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31880,f1466])).

fof(f31880,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31802,f1770])).

fof(f31802,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2957 ),
    inference(resolution,[],[f25913,f288])).

fof(f288,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X2,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f25913,plain,
    ( ~ v1_finset_1(sK11(sK1,sK2,sK3))
    | ~ spl37_2957 ),
    inference(avatar_component_clause,[],[f25912])).

fof(f31932,plain,
    ( spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | spl37_201
    | spl37_281
    | spl37_2957 ),
    inference(avatar_contradiction_clause,[],[f31931])).

fof(f31931,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31930,f223])).

fof(f31930,plain,
    ( v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31929,f226])).

fof(f31929,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31928,f984])).

fof(f984,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_74 ),
    inference(avatar_component_clause,[],[f983])).

fof(f983,plain,
    ( spl37_74
  <=> r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_74])])).

fof(f31928,plain,
    ( ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31927,f390])).

fof(f31927,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31923,f393])).

fof(f31923,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(resolution,[],[f31858,f316])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK14(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK14(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f31858,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31823,f29869])).

fof(f31823,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(resolution,[],[f31814,f984])).

fof(f31814,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31813,f223])).

fof(f31813,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31812,f224])).

fof(f31812,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31811,f225])).

fof(f31811,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31810,f226])).

fof(f31810,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31809,f227])).

fof(f31809,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31808,f228])).

fof(f31808,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31807,f1466])).

fof(f31807,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31804,f1770])).

fof(f31804,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2957 ),
    inference(resolution,[],[f25913,f300])).

fof(f300,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f31879,plain,
    ( ~ spl37_3049
    | spl37_120
    | spl37_201
    | spl37_2957 ),
    inference(avatar_split_clause,[],[f31878,f25912,f1465,f1223,f27416])).

fof(f27416,plain,
    ( spl37_3049
  <=> ~ sP35(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3049])])).

fof(f1223,plain,
    ( spl37_120
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X1)
        | r2_lattice3(sK1,sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_120])])).

fof(f31878,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31877,f223])).

fof(f31877,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31876,f224])).

fof(f31876,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31875,f225])).

fof(f31875,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31874,f226])).

fof(f31874,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31873,f227])).

fof(f31873,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31872,f228])).

fof(f31872,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f31806,f1466])).

fof(f31806,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP35(sK3,sK2,sK1) )
    | ~ spl37_2957 ),
    inference(resolution,[],[f25913,f382])).

fof(f382,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP35(X2,X1,X0) ) ),
    inference(general_splitting,[],[f289,f381_D])).

fof(f381,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP35(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f381_D])).

fof(f381_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP35(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP35])])).

fof(f289,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v1_finset_1(sK11(X0,X1,X2))
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f31798,plain,
    ( spl37_280
    | spl37_172
    | spl37_201
    | ~ spl37_2958 ),
    inference(avatar_split_clause,[],[f31797,f25918,f1465,f1375,f1772])).

fof(f1772,plain,
    ( spl37_280
  <=> r2_hidden(sK12(sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_280])])).

fof(f1375,plain,
    ( spl37_172
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK3,X1)
        | r2_lattice3(sK1,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_172])])).

fof(f31797,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31796,f223])).

fof(f31796,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31795,f224])).

fof(f31795,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31794,f225])).

fof(f31794,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31793,f226])).

fof(f31793,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31792,f227])).

fof(f31792,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31791,f228])).

fof(f31791,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30233,f1466])).

fof(f30233,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f309])).

fof(f309,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f31775,plain,
    ( spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | spl37_77
    | spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(avatar_contradiction_clause,[],[f31774])).

fof(f31774,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_77
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31773,f987])).

fof(f987,plain,
    ( ~ r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_77 ),
    inference(avatar_component_clause,[],[f986])).

fof(f986,plain,
    ( spl37_77
  <=> ~ r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_77])])).

fof(f31773,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f31737,f29869])).

fof(f31737,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_74
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(resolution,[],[f30252,f984])).

fof(f30252,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4) )
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30251,f28512])).

fof(f28512,plain,
    ( sP28(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28511,f27926])).

fof(f27926,plain,
    ( m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f19753])).

fof(f19753,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f231,f503])).

fof(f503,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK3)
      | m1_subset_1(X12,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f228,f337])).

fof(f337,plain,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t53_waybel_0.p',t4_subset)).

fof(f231,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK2)) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f1773,plain,
    ( r2_hidden(sK12(sK1,sK2,sK3),sK3)
    | ~ spl37_280 ),
    inference(avatar_component_clause,[],[f1772])).

fof(f28511,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP28(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f28036])).

fof(f28036,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | sP28(X1,X0,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28035,f27930])).

fof(f27930,plain,
    ( v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f2613])).

fof(f2613,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | v1_finset_1(sK4(X4)) ) ),
    inference(subsumption_resolution,[],[f230,f503])).

fof(f230,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | v1_finset_1(sK4(X4)) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f28035,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP28(X1,X0,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28025,f27929])).

fof(f27929,plain,
    ( r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f2612])).

fof(f2612,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | r1_yellow_0(sK1,sK4(X4)) ) ),
    inference(subsumption_resolution,[],[f232,f503])).

fof(f232,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | r1_yellow_0(sK1,sK4(X4)) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f28025,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP28(X1,X0,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f367,f27928])).

fof(f27928,plain,
    ( k1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) = sK12(sK1,sK2,sK3)
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f2611])).

fof(f2611,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | k1_yellow_0(sK1,sK4(X4)) = X4 ) ),
    inference(subsumption_resolution,[],[f233,f503])).

fof(f233,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(X4,sK3)
      | k1_yellow_0(sK1,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f171])).

fof(f367,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP28(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f367_D])).

fof(f367_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP28(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP28])])).

fof(f30251,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30250,f223])).

fof(f30250,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30249,f224])).

fof(f30249,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30248,f225])).

fof(f30248,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30247,f226])).

fof(f30247,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30246,f227])).

fof(f30246,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30245,f228])).

fof(f30245,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f30234,f1466])).

fof(f30234,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f368])).

fof(f368,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP28(X2,X1,X0) ) ),
    inference(general_splitting,[],[f310,f367_D])).

fof(f310,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f30132,plain,
    ( spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_120 ),
    inference(avatar_contradiction_clause,[],[f30131])).

fof(f30131,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_120 ),
    inference(subsumption_resolution,[],[f30130,f223])).

fof(f30130,plain,
    ( v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_120 ),
    inference(subsumption_resolution,[],[f30129,f226])).

fof(f30129,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_120 ),
    inference(subsumption_resolution,[],[f30128,f30124])).

fof(f30124,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76
    | ~ spl37_120 ),
    inference(subsumption_resolution,[],[f30121,f29869])).

fof(f30121,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_76
    | ~ spl37_120 ),
    inference(resolution,[],[f1224,f990])).

fof(f1224,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1) )
    | ~ spl37_120 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f30128,plain,
    ( ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_76 ),
    inference(subsumption_resolution,[],[f30127,f390])).

fof(f30127,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_2
    | ~ spl37_76 ),
    inference(subsumption_resolution,[],[f30085,f393])).

fof(f30085,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_76 ),
    inference(resolution,[],[f990,f316])).

fof(f30084,plain,
    ( spl37_74
    | spl37_76
    | spl37_1
    | ~ spl37_2 ),
    inference(avatar_split_clause,[],[f29928,f392,f389,f989,f983])).

fof(f29928,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2 ),
    inference(resolution,[],[f29867,f390])).

fof(f29867,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK1,X1)
        | r2_lattice3(sK1,X1,sK14(sK1,sK3,X1))
        | r2_lattice3(sK1,sK3,sK14(sK1,sK3,X1)) )
    | ~ spl37_2 ),
    inference(subsumption_resolution,[],[f29866,f223])).

fof(f29866,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK1,X1)
        | r2_lattice3(sK1,X1,sK14(sK1,sK3,X1))
        | r2_lattice3(sK1,sK3,sK14(sK1,sK3,X1))
        | v2_struct_0(sK1) )
    | ~ spl37_2 ),
    inference(subsumption_resolution,[],[f29863,f226])).

fof(f29863,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK1,X1)
        | r2_lattice3(sK1,X1,sK14(sK1,sK3,X1))
        | r2_lattice3(sK1,sK3,sK14(sK1,sK3,X1))
        | ~ l1_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2 ),
    inference(resolution,[],[f393,f315])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK14(X0,X1,X2))
      | r2_lattice3(X0,X1,sK14(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f30079,plain,
    ( spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(avatar_contradiction_clause,[],[f30078])).

fof(f30078,plain,
    ( $false
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f30077,f223])).

fof(f30077,plain,
    ( v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f30076,f226])).

fof(f30076,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f30075,f984])).

fof(f30075,plain,
    ( ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f30074,f390])).

fof(f30074,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f30071,f393])).

fof(f30071,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK3,sK14(sK1,sK3,sK2))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(resolution,[],[f29905,f316])).

fof(f29905,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_1
    | ~ spl37_2
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f27808,f29869])).

fof(f27808,plain,
    ( ~ m1_subset_1(sK14(sK1,sK3,sK2),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK3,sK2))
    | ~ spl37_74
    | ~ spl37_172 ),
    inference(resolution,[],[f1376,f984])).

fof(f1376,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X1) )
    | ~ spl37_172 ),
    inference(avatar_component_clause,[],[f1375])).

fof(f29306,plain,
    ( spl37_241
    | ~ spl37_280 ),
    inference(avatar_contradiction_clause,[],[f29305])).

fof(f29305,plain,
    ( $false
    | ~ spl37_241
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f1594,f29304])).

fof(f29304,plain,
    ( sP34(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f29294,f27926])).

fof(f29294,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP34(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f28048])).

fof(f28048,plain,
    ( ! [X12,X13] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X12,X13)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X12))
        | sP34(X13,X12,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28047,f27930])).

fof(f28047,plain,
    ( ! [X12,X13] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X12,X13)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X12))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP34(X13,X12,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28031,f27929])).

fof(f28031,plain,
    ( ! [X12,X13] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X12,X13)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X12))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP34(X13,X12,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f379,f27928])).

fof(f379,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP34(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f379_D])).

fof(f379_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP34(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP34])])).

fof(f1594,plain,
    ( ~ sP34(sK3,sK2,sK1)
    | ~ spl37_241 ),
    inference(avatar_component_clause,[],[f1593])).

fof(f1593,plain,
    ( spl37_241
  <=> ~ sP34(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_241])])).

fof(f29303,plain,
    ( ~ spl37_241
    | spl37_202
    | spl37_120
    | spl37_201 ),
    inference(avatar_split_clause,[],[f29302,f1465,f1223,f1474,f1593])).

fof(f29302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
        | r2_lattice3(sK1,sK3,X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ sP34(sK3,sK2,sK1) )
    | ~ spl37_201 ),
    inference(subsumption_resolution,[],[f1579,f1466])).

fof(f1579,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | sP0(sK1,sK2)
      | r2_lattice3(sK1,sK3,X0)
      | ~ r2_lattice3(sK1,sK2,X0)
      | ~ sP34(sK3,sK2,sK1) ) ),
    inference(resolution,[],[f529,f227])).

fof(f529,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r2_lattice3(sK1,sK3,X11)
      | ~ r2_lattice3(sK1,X10,X11)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f528,f223])).

fof(f528,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r2_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f527,f224])).

fof(f527,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r2_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f526,f225])).

fof(f526,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r2_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f497,f226])).

fof(f497,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK1,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X10,sK3),k1_zfmisc_1(X10))
      | sP0(sK1,X10)
      | r2_lattice3(sK1,sK3,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP34(sK3,X10,sK1) ) ),
    inference(resolution,[],[f228,f380])).

fof(f380,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | sP0(X0,X1)
      | r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP34(X2,X1,X0) ) ),
    inference(general_splitting,[],[f292,f379_D])).

fof(f292,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f29299,plain,
    ( ~ spl37_280
    | spl37_3049 ),
    inference(avatar_contradiction_clause,[],[f29298])).

fof(f29298,plain,
    ( $false
    | ~ spl37_280
    | ~ spl37_3049 ),
    inference(subsumption_resolution,[],[f29297,f27417])).

fof(f27417,plain,
    ( ~ sP35(sK3,sK2,sK1)
    | ~ spl37_3049 ),
    inference(avatar_component_clause,[],[f27416])).

fof(f29297,plain,
    ( sP35(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f29296,f27926])).

fof(f29296,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP35(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f28050])).

fof(f28050,plain,
    ( ! [X14,X15] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X14,X15)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X14))
        | sP35(X15,X14,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28049,f27930])).

fof(f28049,plain,
    ( ! [X14,X15] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X14,X15)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X14))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP35(X15,X14,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28032,f27929])).

fof(f28032,plain,
    ( ! [X14,X15] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X14,X15)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X14))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP35(X15,X14,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f381,f27928])).

fof(f28594,plain,
    ( ~ spl37_280
    | spl37_3113 ),
    inference(avatar_contradiction_clause,[],[f28593])).

fof(f28593,plain,
    ( $false
    | ~ spl37_280
    | ~ spl37_3113 ),
    inference(subsumption_resolution,[],[f28592,f28589])).

fof(f28589,plain,
    ( ~ sP33(sK3,sK2,sK1)
    | ~ spl37_3113 ),
    inference(avatar_component_clause,[],[f28588])).

fof(f28588,plain,
    ( spl37_3113
  <=> ~ sP33(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3113])])).

fof(f28592,plain,
    ( sP33(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28591,f27926])).

fof(f28591,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP33(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f28046])).

fof(f28046,plain,
    ( ! [X10,X11] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X10,X11)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X10))
        | sP33(X11,X10,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28045,f27930])).

fof(f28045,plain,
    ( ! [X10,X11] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X10,X11)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X10))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP33(X11,X10,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28030,f27929])).

fof(f28030,plain,
    ( ! [X10,X11] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X10,X11)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X10))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP33(X11,X10,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f377,f27928])).

fof(f377,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP33(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f377_D])).

fof(f377_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP33(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP33])])).

fof(f28590,plain,
    ( ~ spl37_3113
    | spl37_120
    | spl37_201
    | ~ spl37_2960 ),
    inference(avatar_split_clause,[],[f28583,f25924,f1465,f1223,f28588])).

fof(f28583,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28582,f223])).

fof(f28582,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28581,f224])).

fof(f28581,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28580,f225])).

fof(f28580,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28579,f226])).

fof(f28579,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28578,f227])).

fof(f28578,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28577,f228])).

fof(f28577,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f28571,f1466])).

fof(f28571,plain,
    ( ! [X16] :
        ( ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(trivial_inequality_removal,[],[f28569])).

fof(f28569,plain,
    ( ! [X16] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r2_lattice3(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X16)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP33(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(superposition,[],[f378,f25925])).

fof(f378,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP33(X2,X1,X0) ) ),
    inference(general_splitting,[],[f364,f377_D])).

fof(f364,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | o_0_0_xboole_0 != sK11(X0,X1,X2)
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f295,f239])).

fof(f295,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 != sK11(X0,X1,X2)
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f28530,plain,
    ( ~ spl37_280
    | spl37_3075 ),
    inference(avatar_contradiction_clause,[],[f28529])).

fof(f28529,plain,
    ( $false
    | ~ spl37_280
    | ~ spl37_3075 ),
    inference(subsumption_resolution,[],[f28528,f27995])).

fof(f27995,plain,
    ( ~ sP32(sK3,sK2,sK1)
    | ~ spl37_3075 ),
    inference(avatar_component_clause,[],[f27994])).

fof(f27994,plain,
    ( spl37_3075
  <=> ~ sP32(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3075])])).

fof(f28528,plain,
    ( sP32(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28527,f27926])).

fof(f28527,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP32(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f28044])).

fof(f28044,plain,
    ( ! [X8,X9] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X8,X9)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X8))
        | sP32(X9,X8,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28043,f27930])).

fof(f28043,plain,
    ( ! [X8,X9] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X8,X9)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X8))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP32(X9,X8,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28029,f27929])).

fof(f28029,plain,
    ( ! [X8,X9] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X8,X9)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X8))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP32(X9,X8,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f375,f27928])).

fof(f375,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP32(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f375_D])).

fof(f375_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP32(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP32])])).

fof(f28519,plain,
    ( ~ spl37_280
    | spl37_3011 ),
    inference(avatar_contradiction_clause,[],[f28518])).

fof(f28518,plain,
    ( $false
    | ~ spl37_280
    | ~ spl37_3011 ),
    inference(subsumption_resolution,[],[f28517,f26732])).

fof(f26732,plain,
    ( ~ sP29(sK3,sK2,sK1)
    | ~ spl37_3011 ),
    inference(avatar_component_clause,[],[f26731])).

fof(f26731,plain,
    ( spl37_3011
  <=> ~ sP29(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3011])])).

fof(f28517,plain,
    ( sP29(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28516,f27926])).

fof(f28516,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP29(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f28038])).

fof(f28038,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | sP29(X3,X2,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28037,f27930])).

fof(f28037,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP29(X3,X2,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f28026,f27929])).

fof(f28026,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP29(X3,X2,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f369,f27928])).

fof(f369,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP29(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f369_D])).

fof(f369_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP29(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP29])])).

fof(f27996,plain,
    ( ~ spl37_3075
    | spl37_120
    | spl37_201
    | ~ spl37_2958 ),
    inference(avatar_split_clause,[],[f27989,f25918,f1465,f1223,f27994])).

fof(f27989,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27988,f223])).

fof(f27988,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27987,f224])).

fof(f27987,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27986,f225])).

fof(f27986,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27985,f226])).

fof(f27985,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27984,f227])).

fof(f27984,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27983,f228])).

fof(f27983,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27973,f1466])).

fof(f27973,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X5)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP32(sK3,sK2,sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f376])).

fof(f376,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X2,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP32(X2,X1,X0) ) ),
    inference(general_splitting,[],[f298,f375_D])).

fof(f298,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k1_yellow_0(X0,sK11(X0,X1,X2)),X2)
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f27912,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_94
    | spl37_97
    | spl37_201
    | spl37_281
    | ~ spl37_2960 ),
    inference(avatar_contradiction_clause,[],[f27911])).

fof(f27911,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_97
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27910,f1087])).

fof(f1087,plain,
    ( ~ r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_97 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1086,plain,
    ( spl37_97
  <=> ~ r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_97])])).

fof(f27910,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27885,f19944])).

fof(f19944,plain,
    ( m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl37_0
    | ~ spl37_3 ),
    inference(resolution,[],[f19762,f396])).

fof(f396,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | ~ spl37_3 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl37_3
  <=> ~ r1_yellow_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3])])).

fof(f19762,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK1,X0)
        | m1_subset_1(sK14(sK1,sK2,X0),u1_struct_0(sK1)) )
    | ~ spl37_0 ),
    inference(subsumption_resolution,[],[f19761,f223])).

fof(f19761,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK1,X0)
        | m1_subset_1(sK14(sK1,sK2,X0),u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl37_0 ),
    inference(subsumption_resolution,[],[f19759,f226])).

fof(f19759,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK1,X0)
        | m1_subset_1(sK14(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_0 ),
    inference(resolution,[],[f387,f314])).

fof(f387,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ spl37_0 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl37_0
  <=> r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_0])])).

fof(f27885,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_94
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(resolution,[],[f27882,f1084])).

fof(f1084,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_94 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1083,plain,
    ( spl37_94
  <=> r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_94])])).

fof(f27882,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27881,f223])).

fof(f27881,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27880,f224])).

fof(f27880,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27879,f225])).

fof(f27879,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27878,f226])).

fof(f27878,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27877,f227])).

fof(f27877,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27876,f228])).

fof(f27876,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27875,f1466])).

fof(f27875,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f27872,f1770])).

fof(f27872,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(trivial_inequality_removal,[],[f27861])).

fof(f27861,plain,
    ( ! [X10] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r2_lattice3(sK1,sK2,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X10)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(superposition,[],[f365,f25925])).

fof(f27769,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_94
    | spl37_97
    | spl37_201
    | spl37_281
    | ~ spl37_2958 ),
    inference(avatar_contradiction_clause,[],[f27768])).

fof(f27768,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_97
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27767,f1087])).

fof(f27767,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27742,f19944])).

fof(f27742,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_94
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(resolution,[],[f27707,f1084])).

fof(f27707,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27706,f223])).

fof(f27706,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27705,f224])).

fof(f27705,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27704,f225])).

fof(f27704,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27703,f226])).

fof(f27703,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27702,f227])).

fof(f27702,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27701,f228])).

fof(f27701,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27700,f1466])).

fof(f27700,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27686,f1770])).

fof(f27686,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f297])).

fof(f27670,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_94
    | spl37_97
    | spl37_201
    | spl37_281
    | spl37_2957 ),
    inference(avatar_contradiction_clause,[],[f27669])).

fof(f27669,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_97
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27668,f1087])).

fof(f27668,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27638,f19944])).

fof(f27638,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_94
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(resolution,[],[f27426,f1084])).

fof(f27426,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27425,f223])).

fof(f27425,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27424,f224])).

fof(f27424,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27423,f225])).

fof(f27423,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27422,f226])).

fof(f27422,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27421,f227])).

fof(f27421,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27420,f228])).

fof(f27420,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27419,f1466])).

fof(f27419,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27160,f1770])).

fof(f27160,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK3,X1)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2957 ),
    inference(resolution,[],[f25913,f288])).

fof(f27404,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_94
    | spl37_97
    | ~ spl37_120 ),
    inference(avatar_contradiction_clause,[],[f27403])).

fof(f27403,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_97
    | ~ spl37_120 ),
    inference(subsumption_resolution,[],[f27402,f1087])).

fof(f27402,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_120 ),
    inference(subsumption_resolution,[],[f27392,f19944])).

fof(f27392,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_94
    | ~ spl37_120 ),
    inference(resolution,[],[f1084,f1224])).

fof(f27301,plain,
    ( spl37_94
    | spl37_96
    | ~ spl37_0
    | spl37_3 ),
    inference(avatar_split_clause,[],[f19962,f395,f386,f1089,f1083])).

fof(f1089,plain,
    ( spl37_96
  <=> r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_96])])).

fof(f19962,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3 ),
    inference(resolution,[],[f19764,f396])).

fof(f19764,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK1,X1)
        | r2_lattice3(sK1,X1,sK14(sK1,sK2,X1))
        | r2_lattice3(sK1,sK2,sK14(sK1,sK2,X1)) )
    | ~ spl37_0 ),
    inference(subsumption_resolution,[],[f19763,f223])).

fof(f19763,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK1,X1)
        | r2_lattice3(sK1,X1,sK14(sK1,sK2,X1))
        | r2_lattice3(sK1,sK2,sK14(sK1,sK2,X1))
        | v2_struct_0(sK1) )
    | ~ spl37_0 ),
    inference(subsumption_resolution,[],[f19760,f226])).

fof(f19760,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK1,X1)
        | r2_lattice3(sK1,X1,sK14(sK1,sK2,X1))
        | r2_lattice3(sK1,sK2,sK14(sK1,sK2,X1))
        | ~ l1_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_0 ),
    inference(resolution,[],[f387,f315])).

fof(f27226,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_96
    | spl37_201
    | spl37_281
    | spl37_2957 ),
    inference(avatar_contradiction_clause,[],[f27225])).

fof(f27225,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27224,f25892])).

fof(f25892,plain,
    ( ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96 ),
    inference(subsumption_resolution,[],[f25891,f223])).

fof(f25891,plain,
    ( ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96 ),
    inference(subsumption_resolution,[],[f25890,f226])).

fof(f25890,plain,
    ( ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96 ),
    inference(subsumption_resolution,[],[f25889,f396])).

fof(f25889,plain,
    ( r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_0
    | ~ spl37_96 ),
    inference(subsumption_resolution,[],[f20367,f387])).

fof(f20367,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl37_96 ),
    inference(resolution,[],[f1090,f316])).

fof(f1090,plain,
    ( r2_lattice3(sK1,sK3,sK14(sK1,sK2,sK3))
    | ~ spl37_96 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f27224,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27176,f19944])).

fof(f27176,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(resolution,[],[f27172,f1090])).

fof(f27172,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27171,f223])).

fof(f27171,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27170,f224])).

fof(f27170,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27169,f225])).

fof(f27169,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27168,f226])).

fof(f27168,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27167,f227])).

fof(f27167,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27166,f228])).

fof(f27166,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27165,f1466])).

fof(f27165,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f27162,f1770])).

fof(f27162,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2957 ),
    inference(resolution,[],[f25913,f300])).

fof(f27150,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_96
    | spl37_201
    | spl37_281
    | ~ spl37_2958 ),
    inference(avatar_contradiction_clause,[],[f27149])).

fof(f27149,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27148,f25892])).

fof(f27148,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f27100,f19944])).

fof(f27100,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(resolution,[],[f26920,f1090])).

fof(f26920,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26919,f223])).

fof(f26919,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26918,f224])).

fof(f26918,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26917,f225])).

fof(f26917,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26916,f226])).

fof(f26916,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26915,f227])).

fof(f26915,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26914,f228])).

fof(f26914,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_201
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26913,f1466])).

fof(f26913,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_281
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26901,f1770])).

fof(f26901,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK1,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X3)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f309])).

fof(f26801,plain,
    ( spl37_202
    | spl37_172
    | spl37_201
    | spl37_281 ),
    inference(avatar_split_clause,[],[f26800,f1769,f1465,f1375,f1474])).

fof(f26800,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
        | r2_lattice3(sK1,sK2,X3)
        | ~ r2_lattice3(sK1,sK3,X3) )
    | ~ spl37_201
    | ~ spl37_281 ),
    inference(subsumption_resolution,[],[f26799,f1466])).

fof(f26799,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
        | sP0(sK1,sK2)
        | r2_lattice3(sK1,sK2,X3)
        | ~ r2_lattice3(sK1,sK3,X3) )
    | ~ spl37_281 ),
    inference(subsumption_resolution,[],[f19768,f1770])).

fof(f19768,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | r2_hidden(sK12(sK1,sK2,sK3),sK3)
      | sP0(sK1,sK2)
      | r2_lattice3(sK1,sK2,X3)
      | ~ r2_lattice3(sK1,sK3,X3) ) ),
    inference(resolution,[],[f227,f521])).

fof(f521,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r2_lattice3(sK1,X7,X6)
      | ~ r2_lattice3(sK1,sK3,X6) ) ),
    inference(subsumption_resolution,[],[f520,f223])).

fof(f520,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r2_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f519,f224])).

fof(f519,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r2_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f518,f225])).

fof(f518,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r2_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f495,f226])).

fof(f495,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK1,sK3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X7,sK3),k1_zfmisc_1(X7))
      | r2_hidden(sK12(sK1,X7,sK3),sK3)
      | sP0(sK1,X7)
      | r2_lattice3(sK1,X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f228,f303])).

fof(f303,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f26761,plain,
    ( spl37_200
    | spl37_280
    | spl37_172
    | ~ spl37_2960 ),
    inference(avatar_split_clause,[],[f26760,f25924,f1375,f1772,f1468])).

fof(f1468,plain,
    ( spl37_200
  <=> sP0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_200])])).

fof(f26760,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26759,f223])).

fof(f26759,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26758,f224])).

fof(f26758,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26757,f225])).

fof(f26757,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26756,f226])).

fof(f26756,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26755,f227])).

fof(f26755,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26538,f228])).

fof(f26538,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(trivial_inequality_removal,[],[f26523])).

fof(f26523,plain,
    ( ! [X8] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r2_lattice3(sK1,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X8)
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl37_2960 ),
    inference(superposition,[],[f362,f25925])).

fof(f362,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X3)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f306,f239])).

fof(f306,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
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
    inference(cnf_transformation,[],[f190])).

fof(f26733,plain,
    ( ~ spl37_3011
    | spl37_200
    | spl37_172
    | ~ spl37_2960 ),
    inference(avatar_split_clause,[],[f26726,f25924,f1375,f1468,f26731])).

fof(f26726,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26725,f223])).

fof(f26725,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26724,f224])).

fof(f26724,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26723,f225])).

fof(f26723,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26722,f226])).

fof(f26722,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26721,f227])).

fof(f26721,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26534,f228])).

fof(f26534,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(trivial_inequality_removal,[],[f26528])).

fof(f26528,plain,
    ( ! [X13] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(superposition,[],[f370,f25925])).

fof(f370,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != sK11(X0,X1,X2)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP29(X2,X1,X0) ) ),
    inference(general_splitting,[],[f361,f369_D])).

fof(f361,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | o_0_0_xboole_0 != sK11(X0,X1,X2)
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f307,f239])).

fof(f307,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 != sK11(X0,X1,X2)
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f26701,plain,
    ( ~ spl37_200
    | ~ spl37_2998 ),
    inference(avatar_contradiction_clause,[],[f26700])).

fof(f26700,plain,
    ( $false
    | ~ spl37_200
    | ~ spl37_2998 ),
    inference(subsumption_resolution,[],[f26699,f1469])).

fof(f1469,plain,
    ( sP0(sK1,sK2)
    | ~ spl37_200 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f26699,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_2998 ),
    inference(trivial_inequality_removal,[],[f26697])).

fof(f26697,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | ~ sP0(sK1,sK2)
    | ~ spl37_2998 ),
    inference(superposition,[],[f360,f26566])).

fof(f26566,plain,
    ( o_0_0_xboole_0 = sK10(sK1,sK2)
    | ~ spl37_2998 ),
    inference(avatar_component_clause,[],[f26565])).

fof(f26565,plain,
    ( spl37_2998
  <=> o_0_0_xboole_0 = sK10(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2998])])).

fof(f360,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != sK10(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f285,f239])).

fof(f285,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK10(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,sK10(X0,X1))
        & k1_xboole_0 != sK10(X0,X1)
        & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK10(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f183,f184])).

fof(f184,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r1_yellow_0(X0,sK10(X0,X1))
        & k1_xboole_0 != sK10(X0,X1)
        & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK10(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f163])).

fof(f26644,plain,
    ( ~ spl37_200
    | ~ spl37_3000 ),
    inference(avatar_contradiction_clause,[],[f26643])).

fof(f26643,plain,
    ( $false
    | ~ spl37_200
    | ~ spl37_3000 ),
    inference(subsumption_resolution,[],[f26640,f1469])).

fof(f26640,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_3000 ),
    inference(resolution,[],[f26573,f286])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,sK10(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f26573,plain,
    ( r1_yellow_0(sK1,sK10(sK1,sK2))
    | ~ spl37_3000 ),
    inference(avatar_component_clause,[],[f26572])).

fof(f26572,plain,
    ( spl37_3000
  <=> r1_yellow_0(sK1,sK10(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_3000])])).

fof(f26594,plain,
    ( ~ spl37_200
    | spl37_2995 ),
    inference(avatar_contradiction_clause,[],[f26593])).

fof(f26593,plain,
    ( $false
    | ~ spl37_200
    | ~ spl37_2995 ),
    inference(subsumption_resolution,[],[f26592,f1469])).

fof(f26592,plain,
    ( ~ sP0(sK1,sK2)
    | ~ spl37_2995 ),
    inference(resolution,[],[f26554,f283])).

fof(f283,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK10(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f26554,plain,
    ( ~ v1_finset_1(sK10(sK1,sK2))
    | ~ spl37_2995 ),
    inference(avatar_component_clause,[],[f26553])).

fof(f26553,plain,
    ( spl37_2995
  <=> ~ v1_finset_1(sK10(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2995])])).

fof(f26574,plain,
    ( ~ spl37_2995
    | spl37_3000
    | spl37_2998
    | ~ spl37_200 ),
    inference(avatar_split_clause,[],[f26540,f1468,f26565,f26572,f26553])).

fof(f26540,plain,
    ( o_0_0_xboole_0 = sK10(sK1,sK2)
    | r1_yellow_0(sK1,sK10(sK1,sK2))
    | ~ v1_finset_1(sK10(sK1,sK2))
    | ~ spl37_200 ),
    inference(resolution,[],[f26488,f357])).

fof(f357,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
      | o_0_0_xboole_0 = X6
      | r1_yellow_0(sK1,X6)
      | ~ v1_finset_1(X6) ) ),
    inference(definition_unfolding,[],[f229,f239])).

fof(f229,plain,(
    ! [X6] :
      ( r1_yellow_0(sK1,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f26488,plain,
    ( m1_subset_1(sK10(sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl37_200 ),
    inference(resolution,[],[f1469,f284])).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_subset_1(sK10(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f26342,plain,
    ( ~ spl37_280
    | spl37_2977 ),
    inference(avatar_contradiction_clause,[],[f26341])).

fof(f26341,plain,
    ( $false
    | ~ spl37_280
    | ~ spl37_2977 ),
    inference(subsumption_resolution,[],[f26340,f26305])).

fof(f26305,plain,
    ( ~ sP31(sK3,sK2,sK1)
    | ~ spl37_2977 ),
    inference(avatar_component_clause,[],[f26304])).

fof(f26304,plain,
    ( spl37_2977
  <=> ~ sP31(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_2977])])).

fof(f26340,plain,
    ( sP31(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f26339,f20322])).

fof(f20322,plain,
    ( m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f19753])).

fof(f26339,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP31(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f21954])).

fof(f21954,plain,
    ( ! [X6,X7] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X6,X7)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X6))
        | sP31(X7,X6,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21953,f20326])).

fof(f20326,plain,
    ( v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f2613])).

fof(f21953,plain,
    ( ! [X6,X7] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X6,X7)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X6))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP31(X7,X6,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21940,f20325])).

fof(f20325,plain,
    ( r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f2612])).

fof(f21940,plain,
    ( ! [X6,X7] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X6,X7)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X6))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP31(X7,X6,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f373,f20324])).

fof(f20324,plain,
    ( k1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3))) = sK12(sK1,sK2,sK3)
    | ~ spl37_280 ),
    inference(resolution,[],[f1773,f2611])).

fof(f373,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP31(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f373_D])).

fof(f373_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP31(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP31])])).

fof(f26306,plain,
    ( ~ spl37_2977
    | spl37_172
    | spl37_201
    | spl37_2957 ),
    inference(avatar_split_clause,[],[f26299,f25912,f1465,f1375,f26304])).

fof(f26299,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26298,f223])).

fof(f26298,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26297,f224])).

fof(f26297,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26296,f225])).

fof(f26296,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26295,f226])).

fof(f26295,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26294,f227])).

fof(f26294,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26293,f228])).

fof(f26293,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2957 ),
    inference(subsumption_resolution,[],[f26291,f1466])).

fof(f26291,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP31(sK3,sK2,sK1) )
    | ~ spl37_2957 ),
    inference(resolution,[],[f25913,f374])).

fof(f374,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_finset_1(sK11(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X3)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP31(X2,X1,X0) ) ),
    inference(general_splitting,[],[f301,f373_D])).

fof(f301,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v1_finset_1(sK11(X0,X1,X2))
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f26246,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_96
    | spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(avatar_contradiction_clause,[],[f26245])).

fof(f26245,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26244,f25892])).

fof(f26244,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26200,f19944])).

fof(f26200,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(resolution,[],[f26112,f1090])).

fof(f26112,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4) )
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26111,f25881])).

fof(f25881,plain,
    ( sP28(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f25880,f20322])).

fof(f25880,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP28(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f21948])).

fof(f21948,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | sP28(X1,X0,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21947,f20326])).

fof(f21947,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP28(X1,X0,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21937,f20325])).

fof(f21937,plain,
    ( ! [X0,X1] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X0,X1)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP28(X1,X0,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f367,f20324])).

fof(f26111,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26110,f223])).

fof(f26110,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26109,f224])).

fof(f26109,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26108,f225])).

fof(f26108,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26107,f226])).

fof(f26107,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26106,f227])).

fof(f26106,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26105,f228])).

fof(f26105,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2958 ),
    inference(subsumption_resolution,[],[f26094,f1466])).

fof(f26094,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK1,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP28(sK3,sK2,sK1) )
    | ~ spl37_2958 ),
    inference(resolution,[],[f25919,f368])).

fof(f26052,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_96
    | spl37_201
    | ~ spl37_280
    | ~ spl37_2960 ),
    inference(avatar_contradiction_clause,[],[f26051])).

fof(f26051,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26050,f25892])).

fof(f26050,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f26006,f19944])).

fof(f26006,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_96
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2960 ),
    inference(resolution,[],[f26000,f1090])).

fof(f26000,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13) )
    | ~ spl37_201
    | ~ spl37_280
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25999,f25884])).

fof(f25884,plain,
    ( sP29(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f25883,f20322])).

fof(f25883,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP29(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f21950])).

fof(f21950,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | sP29(X3,X2,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21949,f20326])).

fof(f21949,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP29(X3,X2,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21938,f20325])).

fof(f21938,plain,
    ( ! [X2,X3] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X2,X3)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X2))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP29(X3,X2,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f369,f20324])).

fof(f25999,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25998,f223])).

fof(f25998,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25997,f224])).

fof(f25997,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25996,f225])).

fof(f25996,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25995,f226])).

fof(f25995,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25994,f227])).

fof(f25994,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25993,f228])).

fof(f25993,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_2960 ),
    inference(subsumption_resolution,[],[f25988,f1466])).

fof(f25988,plain,
    ( ! [X13] :
        ( ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(trivial_inequality_removal,[],[f25982])).

fof(f25982,plain,
    ( ! [X13] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | ~ r2_lattice3(sK1,sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X13)
        | sP0(sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ sP29(sK3,sK2,sK1) )
    | ~ spl37_2960 ),
    inference(superposition,[],[f370,f25925])).

fof(f25897,plain,
    ( spl37_202
    | spl37_172
    | spl37_201
    | ~ spl37_280 ),
    inference(avatar_split_clause,[],[f25896,f1772,f1465,f1375,f1474])).

fof(f25896,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
        | r2_lattice3(sK1,sK2,X4)
        | ~ r2_lattice3(sK1,sK3,X4) )
    | ~ spl37_201
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f25895,f25886])).

fof(f25886,plain,
    ( sP30(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f25885,f20322])).

fof(f25885,plain,
    ( ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(sK2))
    | sP30(sK3,sK2,sK1)
    | ~ spl37_280 ),
    inference(equality_resolution,[],[f21952])).

fof(f21952,plain,
    ( ! [X4,X5] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X4,X5)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X4))
        | sP30(X5,X4,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21951,f20326])).

fof(f21951,plain,
    ( ! [X4,X5] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X4,X5)
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X4))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP30(X5,X4,sK1) )
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f21939,f20325])).

fof(f21939,plain,
    ( ! [X4,X5] :
        ( sK12(sK1,sK2,sK3) != sK12(sK1,X4,X5)
        | ~ r1_yellow_0(sK1,sK4(sK12(sK1,sK2,sK3)))
        | ~ m1_subset_1(sK4(sK12(sK1,sK2,sK3)),k1_zfmisc_1(X4))
        | ~ v1_finset_1(sK4(sK12(sK1,sK2,sK3)))
        | sP30(X5,X4,sK1) )
    | ~ spl37_280 ),
    inference(superposition,[],[f371,f20324])).

fof(f371,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP30(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f371_D])).

fof(f371_D,plain,(
    ! [X0,X1,X2] :
      ( ! [X6] :
          ( k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
          | ~ r1_yellow_0(X0,X6)
          | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X6) )
    <=> ~ sP30(X2,X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP30])])).

fof(f25895,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
        | r2_lattice3(sK1,sK2,X4)
        | ~ r2_lattice3(sK1,sK3,X4)
        | ~ sP30(sK3,sK2,sK1) )
    | ~ spl37_201 ),
    inference(subsumption_resolution,[],[f19769,f1466])).

fof(f19769,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | sP0(sK1,sK2)
      | r2_lattice3(sK1,sK2,X4)
      | ~ r2_lattice3(sK1,sK3,X4)
      | ~ sP30(sK3,sK2,sK1) ) ),
    inference(resolution,[],[f227,f525])).

fof(f525,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r2_lattice3(sK1,X9,X8)
      | ~ r2_lattice3(sK1,sK3,X8)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f524,f223])).

fof(f524,plain,(
    ! [X8,X9] :
      ( ~ r2_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r2_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f523,f224])).

fof(f523,plain,(
    ! [X8,X9] :
      ( ~ r2_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r2_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f522,f225])).

fof(f522,plain,(
    ! [X8,X9] :
      ( ~ r2_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r2_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f496,f226])).

fof(f496,plain,(
    ! [X8,X9] :
      ( ~ r2_lattice3(sK1,sK3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X9,sK3),k1_zfmisc_1(X9))
      | sP0(sK1,X9)
      | r2_lattice3(sK1,X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ sP30(sK3,X9,sK1) ) ),
    inference(resolution,[],[f228,f372])).

fof(f372,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | sP0(X0,X1)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP30(X2,X1,X0) ) ),
    inference(general_splitting,[],[f304,f371_D])).

fof(f304,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | k1_yellow_0(X0,X6) != sK12(X0,X1,X2)
      | ~ r1_yellow_0(X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X6)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f25894,plain,
    ( ~ spl37_0
    | spl37_3
    | ~ spl37_94
    | ~ spl37_96 ),
    inference(avatar_contradiction_clause,[],[f25893])).

fof(f25893,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_94
    | ~ spl37_96 ),
    inference(subsumption_resolution,[],[f1084,f25892])).

fof(f25888,plain,
    ( spl37_199
    | ~ spl37_280 ),
    inference(avatar_contradiction_clause,[],[f25887])).

fof(f25887,plain,
    ( $false
    | ~ spl37_199
    | ~ spl37_280 ),
    inference(subsumption_resolution,[],[f25886,f1463])).

fof(f1463,plain,
    ( ~ sP30(sK3,sK2,sK1)
    | ~ spl37_199 ),
    inference(avatar_component_clause,[],[f1462])).

fof(f1462,plain,
    ( spl37_199
  <=> ~ sP30(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_199])])).

fof(f20694,plain,
    ( ~ spl37_199
    | spl37_172
    | spl37_201
    | spl37_203 ),
    inference(avatar_split_clause,[],[f20693,f1471,f1465,f1375,f1462])).

fof(f1471,plain,
    ( spl37_203
  <=> ~ m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_203])])).

fof(f20693,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,X4)
        | ~ r2_lattice3(sK1,sK3,X4)
        | ~ sP30(sK3,sK2,sK1) )
    | ~ spl37_201
    | ~ spl37_203 ),
    inference(subsumption_resolution,[],[f20692,f1466])).

fof(f20692,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | sP0(sK1,sK2)
        | r2_lattice3(sK1,sK2,X4)
        | ~ r2_lattice3(sK1,sK3,X4)
        | ~ sP30(sK3,sK2,sK1) )
    | ~ spl37_203 ),
    inference(subsumption_resolution,[],[f19769,f1472])).

fof(f1472,plain,
    ( ~ m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl37_203 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f20689,plain,
    ( ~ spl37_0
    | spl37_3
    | spl37_95
    | ~ spl37_96
    | ~ spl37_172 ),
    inference(avatar_contradiction_clause,[],[f20688])).

fof(f20688,plain,
    ( $false
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_95
    | ~ spl37_96
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f20687,f1081])).

fof(f1081,plain,
    ( ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_95 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f1080,plain,
    ( spl37_95
  <=> ~ r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_95])])).

fof(f20687,plain,
    ( r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_0
    | ~ spl37_3
    | ~ spl37_96
    | ~ spl37_172 ),
    inference(subsumption_resolution,[],[f20666,f19944])).

fof(f20666,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK14(sK1,sK2,sK3))
    | ~ spl37_96
    | ~ spl37_172 ),
    inference(resolution,[],[f1376,f1090])).

fof(f1774,plain,
    ( spl37_280
    | spl37_120
    | spl37_201
    | spl37_203 ),
    inference(avatar_split_clause,[],[f1767,f1471,f1465,f1223,f1772])).

fof(f1767,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | r2_lattice3(sK1,sK3,X0)
        | ~ r2_lattice3(sK1,sK2,X0) )
    | ~ spl37_201
    | ~ spl37_203 ),
    inference(subsumption_resolution,[],[f1766,f1466])).

fof(f1766,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(sK12(sK1,sK2,sK3),sK3)
        | sP0(sK1,sK2)
        | r2_lattice3(sK1,sK3,X0)
        | ~ r2_lattice3(sK1,sK2,X0) )
    | ~ spl37_203 ),
    inference(subsumption_resolution,[],[f1758,f1472])).

fof(f1758,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,sK2,sK3),k1_zfmisc_1(sK2))
      | r2_hidden(sK12(sK1,sK2,sK3),sK3)
      | sP0(sK1,sK2)
      | r2_lattice3(sK1,sK3,X0)
      | ~ r2_lattice3(sK1,sK2,X0) ) ),
    inference(resolution,[],[f513,f227])).

fof(f513,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r2_lattice3(sK1,sK3,X3)
      | ~ r2_lattice3(sK1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f512,f223])).

fof(f512,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r2_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f511,f224])).

fof(f511,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r2_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f510,f225])).

fof(f510,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r2_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f493,f226])).

fof(f493,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK11(sK1,X2,sK3),k1_zfmisc_1(X2))
      | r2_hidden(sK12(sK1,X2,sK3),sK3)
      | sP0(sK1,X2)
      | r2_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f228,f291])).

fof(f291,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(X1))
      | r2_hidden(sK12(X0,X1,X2),X2)
      | sP0(X0,X1)
      | r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f398,plain,
    ( spl37_0
    | spl37_2 ),
    inference(avatar_split_clause,[],[f235,f392,f386])).

fof(f235,plain,
    ( r1_yellow_0(sK1,sK3)
    | r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f171])).

fof(f397,plain,
    ( ~ spl37_1
    | ~ spl37_3 ),
    inference(avatar_split_clause,[],[f236,f395,f389])).

fof(f236,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | ~ r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f171])).
%------------------------------------------------------------------------------

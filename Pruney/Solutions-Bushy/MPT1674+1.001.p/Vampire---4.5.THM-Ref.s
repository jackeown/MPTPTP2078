%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1674+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:19 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  148 (69063 expanded)
%              Number of leaves         :   15 (26656 expanded)
%              Depth                    :   54
%              Number of atoms          : 1024 (1340528 expanded)
%              Number of equality atoms :  142 (250130 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(subsumption_resolution,[],[f284,f275])).

fof(f275,plain,(
    sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f274,f260])).

fof(f260,plain,
    ( sP1(sK5,sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f259,f204])).

fof(f204,plain,
    ( sP2(sK3,sK4,sK5)
    | sP1(sK5,sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f203,f129])).

fof(f129,plain,
    ( r2_lattice3(sK3,sK5,sK10(sK3,sK4,sK5))
    | sP0(sK3,sK4)
    | sP1(sK5,sK3,sK4)
    | sP2(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f57,plain,(
    k1_yellow_0(sK3,sK4) != k1_yellow_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_yellow_0(sK3,sK4) != k1_yellow_0(sK3,sK5)
    & r1_yellow_0(sK3,sK4)
    & ! [X3] :
        ( r2_hidden(k1_yellow_0(sK3,X3),sK5)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK4))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k1_yellow_0(sK3,sK6(X4)) = X4
          & r1_yellow_0(sK3,sK6(X4))
          & m1_subset_1(sK6(X4),k1_zfmisc_1(sK4))
          & v1_finset_1(sK6(X4)) )
        | ~ r2_hidden(X4,sK5)
        | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
    & ! [X6] :
        ( r1_yellow_0(sK3,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK4))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f10,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
                & r1_yellow_0(X0,X1)
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
              ( k1_yellow_0(sK3,X1) != k1_yellow_0(sK3,X2)
              & r1_yellow_0(sK3,X1)
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(sK3,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(sK3,X5) = X4
                      & r1_yellow_0(sK3,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
              & ! [X6] :
                  ( r1_yellow_0(sK3,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_yellow_0(sK3,X1) != k1_yellow_0(sK3,X2)
            & r1_yellow_0(sK3,X1)
            & ! [X3] :
                ( r2_hidden(k1_yellow_0(sK3,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k1_yellow_0(sK3,X5) = X4
                    & r1_yellow_0(sK3,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(X1))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            & ! [X6] :
                ( r1_yellow_0(sK3,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X2] :
          ( k1_yellow_0(sK3,X2) != k1_yellow_0(sK3,sK4)
          & r1_yellow_0(sK3,sK4)
          & ! [X3] :
              ( r2_hidden(k1_yellow_0(sK3,X3),X2)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK4))
              | ~ v1_finset_1(X3) )
          & ! [X4] :
              ( ? [X5] :
                  ( k1_yellow_0(sK3,X5) = X4
                  & r1_yellow_0(sK3,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(sK4))
                  & v1_finset_1(X5) )
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
          & ! [X6] :
              ( r1_yellow_0(sK3,X6)
              | k1_xboole_0 = X6
              | ~ m1_subset_1(X6,k1_zfmisc_1(sK4))
              | ~ v1_finset_1(X6) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k1_yellow_0(sK3,X2) != k1_yellow_0(sK3,sK4)
        & r1_yellow_0(sK3,sK4)
        & ! [X3] :
            ( r2_hidden(k1_yellow_0(sK3,X3),X2)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK4))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k1_yellow_0(sK3,X5) = X4
                & r1_yellow_0(sK3,X5)
                & m1_subset_1(X5,k1_zfmisc_1(sK4))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
        & ! [X6] :
            ( r1_yellow_0(sK3,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(sK4))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( k1_yellow_0(sK3,sK4) != k1_yellow_0(sK3,sK5)
      & r1_yellow_0(sK3,sK4)
      & ! [X3] :
          ( r2_hidden(k1_yellow_0(sK3,X3),sK5)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK4))
          | ~ v1_finset_1(X3) )
      & ! [X4] :
          ( ? [X5] :
              ( k1_yellow_0(sK3,X5) = X4
              & r1_yellow_0(sK3,X5)
              & m1_subset_1(X5,k1_zfmisc_1(sK4))
              & v1_finset_1(X5) )
          | ~ r2_hidden(X4,sK5)
          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
      & ! [X6] :
          ( r1_yellow_0(sK3,X6)
          | k1_xboole_0 = X6
          | ~ m1_subset_1(X6,k1_zfmisc_1(sK4))
          | ~ v1_finset_1(X6) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X4] :
      ( ? [X5] :
          ( k1_yellow_0(sK3,X5) = X4
          & r1_yellow_0(sK3,X5)
          & m1_subset_1(X5,k1_zfmisc_1(sK4))
          & v1_finset_1(X5) )
     => ( k1_yellow_0(sK3,sK6(X4)) = X4
        & r1_yellow_0(sK3,sK6(X4))
        & m1_subset_1(sK6(X4),k1_zfmisc_1(sK4))
        & v1_finset_1(sK6(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_yellow_0(X0,X1)
                    & ! [X3] :
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
                 => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_yellow_0(X0,X1)
                    & ! [X3] :
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
                 => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_yellow_0(X0,X1)
                  & ! [X3] :
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
               => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_waybel_0)).

fof(f124,plain,
    ( r2_lattice3(sK3,sK5,sK10(sK3,sK4,sK5))
    | sP0(sK3,sK4)
    | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,sK5)
    | sP1(sK5,sK3,sK4)
    | sP2(sK3,sK4,sK5) ),
    inference(factoring,[],[f118])).

fof(f118,plain,(
    ! [X1] :
      ( r2_lattice3(sK3,sK5,sK10(sK3,sK4,X1))
      | r2_lattice3(sK3,X1,sK10(sK3,sK4,X1))
      | sP0(sK3,sK4)
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4)
      | sP1(sK5,sK3,sK4)
      | sP2(sK3,sK4,sK5) ) ),
    inference(resolution,[],[f116,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP0(sK3,sK4)
      | sP2(sK3,sK4,X0)
      | r2_lattice3(sK3,X0,sK10(sK3,sK4,X1))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4)
      | sP1(X0,sK3,sK4)
      | r2_lattice3(sK3,X1,sK10(sK3,sK4,X1)) ) ),
    inference(subsumption_resolution,[],[f115,f48])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,(
    ! [X0,X1] :
      ( sP2(sK3,sK4,X0)
      | sP0(sK3,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X0,sK10(sK3,sK4,X1))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4)
      | sP1(X0,sK3,sK4)
      | r2_lattice3(sK3,X1,sK10(sK3,sK4,X1)) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( sP2(sK3,sK4,X0)
      | sP0(sK3,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X0,sK10(sK3,sK4,X1))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4)
      | sP1(X0,sK3,sK4)
      | r2_lattice3(sK3,X1,sK10(sK3,sK4,X1))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4) ) ),
    inference(resolution,[],[f111,f86])).

fof(f86,plain,(
    ! [X0] :
      ( r2_lattice3(sK3,sK4,sK10(sK3,sK4,X0))
      | r2_lattice3(sK3,X0,sK10(sK3,sK4,X0))
      | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,X0) ) ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,(
    r1_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK3,X1)
      | r2_lattice3(sK3,X1,sK10(sK3,X1,X0))
      | r2_lattice3(sK3,X0,sK10(sK3,X1,X0))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_lattice3(sK3,X0,sK10(sK3,X1,X0))
      | r2_lattice3(sK3,X1,sK10(sK3,X1,X0))
      | ~ r1_yellow_0(sK3,X1)
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X2,sK10(X0,X1,X2))
      | r2_lattice3(X0,X1,sK10(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK10(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK10(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK10(X0,X1,X2))
              | r2_lattice3(X0,X1,sK10(X0,X1,X2)) )
            & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK10(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK10(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK10(X0,X1,X2))
          | r2_lattice3(X0,X1,sK10(X0,X1,X2)) )
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X1,sK10(sK3,sK4,X2))
      | sP2(sK3,X1,X0)
      | sP0(sK3,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X0,sK10(sK3,sK4,X2))
      | k1_yellow_0(sK3,X2) = k1_yellow_0(sK3,sK4)
      | sP1(X0,sK3,X1) ) ),
    inference(resolution,[],[f102,f56])).

fof(f102,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_yellow_0(sK3,X5)
      | sP1(X7,sK3,X4)
      | sP2(sK3,X4,X7)
      | sP0(sK3,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X7,sK10(sK3,X5,X6))
      | k1_yellow_0(sK3,X5) = k1_yellow_0(sK3,X6)
      | ~ r2_lattice3(sK3,X4,sK10(sK3,X5,X6)) ) ),
    inference(subsumption_resolution,[],[f101,f44])).

fof(f101,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_lattice3(sK3,X4,sK10(sK3,X5,X6))
      | sP1(X7,sK3,X4)
      | sP2(sK3,X4,X7)
      | sP0(sK3,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X7,sK10(sK3,X5,X6))
      | k1_yellow_0(sK3,X5) = k1_yellow_0(sK3,X6)
      | ~ r1_yellow_0(sK3,X5)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_lattice3(sK3,X4,sK10(sK3,X5,X6))
      | sP1(X7,sK3,X4)
      | sP2(sK3,X4,X7)
      | sP0(sK3,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X7,sK10(sK3,X5,X6))
      | k1_yellow_0(sK3,X5) = k1_yellow_0(sK3,X6)
      | ~ r1_yellow_0(sK3,X5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r2_lattice3(sK3,X0,X1)
      | sP1(X2,sK3,X0)
      | sP2(sK3,X0,X2)
      | sP0(sK3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X2,sK3,X0)
      | sP2(sK3,X0,X2)
      | sP0(sK3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X2,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f45,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X2,sK3,X0)
      | sP2(sK3,X0,X2)
      | sP0(sK3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X2,X1)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f95,f47])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X2,sK3,X0)
      | sP2(sK3,X0,X2)
      | sP0(sK3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_orders_2(sK3)
      | r2_lattice3(sK3,X2,X1)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | sP2(X0,X1,X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X2,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
              | sP2(X0,X1,X2)
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
              | sP2(X0,X1,X2)
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | sP2(X0,X1,X2)
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f19,f18,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_yellow_0(X0,X5) != X4
              | ~ r1_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f203,plain,
    ( sP1(sK5,sK3,sK4)
    | sP2(sK3,sK4,sK5)
    | sP0(sK3,sK4)
    | ~ r2_lattice3(sK3,sK5,sK10(sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f200,f57])).

fof(f200,plain,
    ( sP1(sK5,sK3,sK4)
    | sP2(sK3,sK4,sK5)
    | sP0(sK3,sK4)
    | ~ r2_lattice3(sK3,sK5,sK10(sK3,sK4,sK5))
    | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,sK5) ),
    inference(resolution,[],[f199,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK3,sK4,sK10(sK3,sK4,X0))
      | ~ r2_lattice3(sK3,X0,sK10(sK3,sK4,X0))
      | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,X0) ) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK3,X1)
      | ~ r2_lattice3(sK3,X1,sK10(sK3,X1,X0))
      | ~ r2_lattice3(sK3,X0,sK10(sK3,X1,X0))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK3,X0,sK10(sK3,X1,X0))
      | ~ r2_lattice3(sK3,X1,sK10(sK3,X1,X0))
      | ~ r1_yellow_0(sK3,X1)
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,sK10(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK10(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f199,plain,
    ( r2_lattice3(sK3,sK4,sK10(sK3,sK4,sK5))
    | sP1(sK5,sK3,sK4)
    | sP2(sK3,sK4,sK5)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f196,f57])).

fof(f196,plain,
    ( sP2(sK3,sK4,sK5)
    | sP1(sK5,sK3,sK4)
    | r2_lattice3(sK3,sK4,sK10(sK3,sK4,sK5))
    | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,sK5)
    | sP0(sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( sP2(sK3,sK4,sK5)
    | sP1(sK5,sK3,sK4)
    | r2_lattice3(sK3,sK4,sK10(sK3,sK4,sK5))
    | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,sK5)
    | sP0(sK3,sK4)
    | r2_lattice3(sK3,sK4,sK10(sK3,sK4,sK5))
    | k1_yellow_0(sK3,sK4) = k1_yellow_0(sK3,sK5) ),
    inference(resolution,[],[f182,f86])).

fof(f182,plain,(
    ! [X1] :
      ( ~ r2_lattice3(sK3,sK5,sK10(sK3,sK4,X1))
      | sP2(sK3,sK4,sK5)
      | sP1(sK5,sK3,sK4)
      | r2_lattice3(sK3,sK4,sK10(sK3,sK4,X1))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4)
      | sP0(sK3,sK4) ) ),
    inference(resolution,[],[f177,f49])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP0(sK3,sK4)
      | sP2(sK3,sK4,X0)
      | sP1(X0,sK3,sK4)
      | r2_lattice3(sK3,sK4,sK10(sK3,sK4,X1))
      | k1_yellow_0(sK3,X1) = k1_yellow_0(sK3,sK4)
      | ~ r2_lattice3(sK3,X0,sK10(sK3,sK4,X1)) ) ),
    inference(resolution,[],[f176,f48])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP2(sK3,X1,X0)
      | sP0(sK3,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP1(X0,sK3,X1)
      | r2_lattice3(sK3,X1,sK10(sK3,sK4,X2))
      | k1_yellow_0(sK3,X2) = k1_yellow_0(sK3,sK4)
      | ~ r2_lattice3(sK3,X0,sK10(sK3,sK4,X2)) ) ),
    inference(resolution,[],[f110,f56])).

fof(f110,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_yellow_0(sK3,X5)
      | sP1(X4,sK3,X7)
      | sP2(sK3,X7,X4)
      | sP0(sK3,X7)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X7,sK10(sK3,X5,X6))
      | k1_yellow_0(sK3,X5) = k1_yellow_0(sK3,X6)
      | ~ r2_lattice3(sK3,X4,sK10(sK3,X5,X6)) ) ),
    inference(subsumption_resolution,[],[f109,f44])).

fof(f109,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_lattice3(sK3,X4,sK10(sK3,X5,X6))
      | sP1(X4,sK3,X7)
      | sP2(sK3,X7,X4)
      | sP0(sK3,X7)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X7,sK10(sK3,X5,X6))
      | k1_yellow_0(sK3,X5) = k1_yellow_0(sK3,X6)
      | ~ r1_yellow_0(sK3,X5)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f108,f47])).

fof(f108,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_lattice3(sK3,X4,sK10(sK3,X5,X6))
      | sP1(X4,sK3,X7)
      | sP2(sK3,X7,X4)
      | sP0(sK3,X7)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X7,sK10(sK3,X5,X6))
      | k1_yellow_0(sK3,X5) = k1_yellow_0(sK3,X6)
      | ~ r1_yellow_0(sK3,X5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f106,f72])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r2_lattice3(sK3,X0,X1)
      | sP1(X0,sK3,X2)
      | sP2(sK3,X2,X0)
      | sP0(sK3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X2,X1) ) ),
    inference(subsumption_resolution,[],[f105,f44])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X0,sK3,X2)
      | sP2(sK3,X2,X0)
      | sP0(sK3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X2,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X0,sK3,X2)
      | sP2(sK3,X2,X0)
      | sP0(sK3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_lattice3(sK3,X2,X1)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP1(X0,sK3,X2)
      | sP2(sK3,X2,X0)
      | sP0(sK3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_orders_2(sK3)
      | r2_lattice3(sK3,X2,X1)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f71,f46])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | sP2(X0,X1,X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f259,plain,
    ( ~ sP2(sK3,sK4,sK5)
    | sP1(sK5,sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(equality_resolution,[],[f258])).

fof(f258,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,sK5) != sK7(sK3,sK4,X0)
      | ~ sP2(sK3,sK4,X0)
      | sP1(sK5,sK3,sK4)
      | sP0(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f257,f210])).

fof(f210,plain,
    ( m1_subset_1(sK7(sK3,sK4,sK5),u1_struct_0(sK3))
    | sP0(sK3,sK4)
    | sP1(sK5,sK3,sK4) ),
    inference(resolution,[],[f209,f49])).

fof(f209,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
      | sP1(sK5,sK3,sK4)
      | sP0(sK3,sK4)
      | m1_subset_1(sK7(sK3,sK4,sK5),X0) ) ),
    inference(resolution,[],[f205,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f205,plain,
    ( r2_hidden(sK7(sK3,sK4,sK5),sK5)
    | sP0(sK3,sK4)
    | sP1(sK5,sK3,sK4) ),
    inference(resolution,[],[f204,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( k1_yellow_0(X0,X4) != sK7(X0,X1,X2)
            | ~ r1_yellow_0(X0,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_yellow_0(X0,X4) != X3
              | ~ r1_yellow_0(X0,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X4) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( k1_yellow_0(X0,X4) != sK7(X0,X1,X2)
            | ~ r1_yellow_0(X0,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_yellow_0(X0,X4) != X3
              | ~ r1_yellow_0(X0,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X4) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_yellow_0(X0,X5) != X4
              | ~ r1_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f257,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,sK5) != sK7(sK3,sK4,X0)
      | ~ sP2(sK3,sK4,X0)
      | sP1(sK5,sK3,sK4)
      | sP0(sK3,sK4)
      | ~ m1_subset_1(sK7(sK3,sK4,sK5),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f256,f205])).

fof(f256,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,sK5) != sK7(sK3,sK4,X0)
      | ~ sP2(sK3,sK4,X0)
      | sP1(sK5,sK3,sK4)
      | sP0(sK3,sK4)
      | ~ r2_hidden(sK7(sK3,sK4,sK5),sK5)
      | ~ m1_subset_1(sK7(sK3,sK4,sK5),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f255,f52])).

fof(f52,plain,(
    ! [X4] :
      ( m1_subset_1(sK6(X4),k1_zfmisc_1(sK4))
      | ~ r2_hidden(X4,sK5)
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK7(sK3,sK4,sK5)),k1_zfmisc_1(X0))
      | sK7(sK3,X0,X1) != sK7(sK3,sK4,sK5)
      | ~ sP2(sK3,X0,X1)
      | sP1(sK5,sK3,sK4)
      | sP0(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f254,f212])).

fof(f212,plain,
    ( r1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | sP1(sK5,sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f207,f210])).

fof(f207,plain,
    ( sP0(sK3,sK4)
    | sP1(sK5,sK3,sK4)
    | r1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | ~ m1_subset_1(sK7(sK3,sK4,sK5),u1_struct_0(sK3)) ),
    inference(resolution,[],[f205,f53])).

fof(f53,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5)
      | r1_yellow_0(sK3,sK6(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
      | ~ m1_subset_1(sK6(sK7(sK3,sK4,sK5)),k1_zfmisc_1(X0))
      | sK7(sK3,X0,X1) != sK7(sK3,sK4,sK5)
      | ~ sP2(sK3,X0,X1)
      | sP1(sK5,sK3,sK4)
      | sP0(sK3,sK4) ) ),
    inference(resolution,[],[f253,f211])).

fof(f211,plain,
    ( v1_finset_1(sK6(sK7(sK3,sK4,sK5)))
    | sP1(sK5,sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f208,f210])).

fof(f208,plain,
    ( sP0(sK3,sK4)
    | sP1(sK5,sK3,sK4)
    | v1_finset_1(sK6(sK7(sK3,sK4,sK5)))
    | ~ m1_subset_1(sK7(sK3,sK4,sK5),u1_struct_0(sK3)) ),
    inference(resolution,[],[f205,f51])).

fof(f51,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5)
      | v1_finset_1(sK6(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(sK6(sK7(sK3,sK4,sK5)))
      | ~ r1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
      | ~ m1_subset_1(sK6(sK7(sK3,sK4,sK5)),k1_zfmisc_1(X0))
      | sK7(sK3,X0,X1) != sK7(sK3,sK4,sK5)
      | ~ sP2(sK3,X0,X1) ) ),
    inference(superposition,[],[f61,f247])).

fof(f247,plain,(
    sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5))) ),
    inference(subsumption_resolution,[],[f246,f237])).

fof(f237,plain,
    ( sP0(sK3,sK4)
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5))) ),
    inference(subsumption_resolution,[],[f232,f213])).

fof(f213,plain,
    ( sP1(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5))) ),
    inference(subsumption_resolution,[],[f206,f210])).

fof(f206,plain,
    ( sP0(sK3,sK4)
    | sP1(sK5,sK3,sK4)
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | ~ m1_subset_1(sK7(sK3,sK4,sK5),u1_struct_0(sK3)) ),
    inference(resolution,[],[f205,f54])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5)
      | k1_yellow_0(sK3,sK6(X4)) = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f232,plain,
    ( sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | sP0(sK3,sK4)
    | ~ sP1(sK5,sK3,sK4) ),
    inference(resolution,[],[f231,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X1,sK8(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_yellow_0(X1,sK8(X0,X1,X2)),X0)
        & k1_xboole_0 != sK8(X0,X1,X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK8(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( ~ r2_hidden(k1_yellow_0(X1,sK8(X0,X1,X2)),X0)
        & k1_xboole_0 != sK8(X0,X1,X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f231,plain,
    ( r2_hidden(k1_yellow_0(sK3,sK8(sK5,sK3,sK4)),sK5)
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f230,f213])).

fof(f230,plain,
    ( sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | r2_hidden(k1_yellow_0(sK3,sK8(sK5,sK3,sK4)),sK5)
    | sP0(sK3,sK4)
    | ~ sP1(sK5,sK3,sK4) ),
    inference(resolution,[],[f222,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f222,plain,
    ( ~ m1_subset_1(sK8(sK5,sK3,sK4),k1_zfmisc_1(sK4))
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | r2_hidden(k1_yellow_0(sK3,sK8(sK5,sK3,sK4)),sK5)
    | sP0(sK3,sK4) ),
    inference(resolution,[],[f213,f83])).

fof(f83,plain,(
    ! [X4,X2,X3] :
      ( ~ sP1(X2,X3,X4)
      | r2_hidden(k1_yellow_0(sK3,sK8(X2,X3,X4)),sK5)
      | ~ m1_subset_1(sK8(X2,X3,X4),k1_zfmisc_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK8(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 = sK8(X2,X3,X4)
      | ~ m1_subset_1(sK8(X2,X3,X4),k1_zfmisc_1(sK4))
      | r2_hidden(k1_yellow_0(sK3,sK8(X2,X3,X4)),sK5)
      | ~ sP1(X2,X3,X4) ) ),
    inference(resolution,[],[f55,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK8(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X3] :
      ( ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK4))
      | r2_hidden(k1_yellow_0(sK3,X3),sK5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f246,plain,
    ( sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | ~ sP0(sK3,sK4) ),
    inference(resolution,[],[f241,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,sK9(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,sK9(X0,X1))
        & k1_xboole_0 != sK9(X0,X1)
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK9(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r1_yellow_0(X0,sK9(X0,X1))
        & k1_xboole_0 != sK9(X0,X1)
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK9(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f241,plain,
    ( r1_yellow_0(sK3,sK9(sK3,sK4))
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5))) ),
    inference(subsumption_resolution,[],[f240,f237])).

fof(f240,plain,
    ( r1_yellow_0(sK3,sK9(sK3,sK4))
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5)))
    | ~ sP0(sK3,sK4) ),
    inference(resolution,[],[f239,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f239,plain,
    ( ~ m1_subset_1(sK9(sK3,sK4),k1_zfmisc_1(sK4))
    | r1_yellow_0(sK3,sK9(sK3,sK4))
    | sK7(sK3,sK4,sK5) = k1_yellow_0(sK3,sK6(sK7(sK3,sK4,sK5))) ),
    inference(resolution,[],[f237,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r1_yellow_0(sK3,sK9(X0,X1))
      | ~ m1_subset_1(sK9(X0,X1),k1_zfmisc_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK9(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK9(X0,X1)
      | ~ m1_subset_1(sK9(X0,X1),k1_zfmisc_1(sK4))
      | r1_yellow_0(sK3,sK9(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK9(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X6] :
      ( ~ v1_finset_1(X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK4))
      | r1_yellow_0(sK3,X6) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_yellow_0(X0,X4) != sK7(X0,X1,X2)
      | ~ r1_yellow_0(X0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f274,plain,
    ( sP0(sK3,sK4)
    | ~ sP1(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f273,f65])).

fof(f273,plain,
    ( r2_hidden(k1_yellow_0(sK3,sK8(sK5,sK3,sK4)),sK5)
    | sP0(sK3,sK4)
    | ~ sP1(sK5,sK3,sK4) ),
    inference(resolution,[],[f265,f63])).

fof(f265,plain,
    ( ~ m1_subset_1(sK8(sK5,sK3,sK4),k1_zfmisc_1(sK4))
    | r2_hidden(k1_yellow_0(sK3,sK8(sK5,sK3,sK4)),sK5)
    | sP0(sK3,sK4) ),
    inference(resolution,[],[f260,f83])).

fof(f284,plain,(
    ~ sP0(sK3,sK4) ),
    inference(resolution,[],[f279,f69])).

fof(f279,plain,(
    r1_yellow_0(sK3,sK9(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f278,f275])).

fof(f278,plain,
    ( r1_yellow_0(sK3,sK9(sK3,sK4))
    | ~ sP0(sK3,sK4) ),
    inference(resolution,[],[f277,f67])).

fof(f277,plain,
    ( ~ m1_subset_1(sK9(sK3,sK4),k1_zfmisc_1(sK4))
    | r1_yellow_0(sK3,sK9(sK3,sK4)) ),
    inference(resolution,[],[f275,f78])).

%------------------------------------------------------------------------------

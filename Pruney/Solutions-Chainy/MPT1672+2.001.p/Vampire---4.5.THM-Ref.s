%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:16 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  175 (6403 expanded)
%              Number of leaves         :   25 (1997 expanded)
%              Depth                    :   53
%              Number of atoms          : 1054 (114403 expanded)
%              Number of equality atoms :  128 (14727 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1027,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1013,f78])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1013,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f79,f1011])).

fof(f1011,plain,(
    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f1010,f461])).

fof(f461,plain,
    ( ~ r2_lattice3(sK4,sK6,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f460,f77])).

fof(f77,plain,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | ~ r2_lattice3(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r2_lattice3(sK4,sK6,sK7)
      | ~ r2_lattice3(sK4,sK5,sK7) )
    & ( r2_lattice3(sK4,sK6,sK7)
      | r2_lattice3(sK4,sK5,sK7) )
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & ! [X4] :
        ( r2_hidden(k1_yellow_0(sK4,X4),sK6)
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK5))
        | ~ v1_finset_1(X4) )
    & ! [X5] :
        ( ( k1_yellow_0(sK4,sK8(X5)) = X5
          & r1_yellow_0(sK4,sK8(X5))
          & m1_subset_1(sK8(X5),k1_zfmisc_1(sK5))
          & v1_finset_1(sK8(X5)) )
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
    & ! [X7] :
        ( r1_yellow_0(sK4,X7)
        | k1_xboole_0 = X7
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK5))
        | ~ v1_finset_1(X7) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_orders_2(sK4)
    & v4_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f41,f46,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | r2_lattice3(X0,X1,X3) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X4] :
                    ( r2_hidden(k1_yellow_0(X0,X4),X2)
                    | k1_xboole_0 = X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X4) )
                & ! [X5] :
                    ( ? [X6] :
                        ( k1_yellow_0(X0,X6) = X5
                        & r1_yellow_0(X0,X6)
                        & m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & ! [X7] :
                    ( r1_yellow_0(X0,X7)
                    | k1_xboole_0 = X7
                    | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X7) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK4,X2,X3)
                    | ~ r2_lattice3(sK4,X1,X3) )
                  & ( r2_lattice3(sK4,X2,X3)
                    | r2_lattice3(sK4,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(sK4)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(sK4,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(sK4,X6) = X5
                      & r1_yellow_0(sK4,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
              & ! [X7] :
                  ( r1_yellow_0(sK4,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_orders_2(sK4)
      & v4_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(sK4,X2,X3)
                  | ~ r2_lattice3(sK4,X1,X3) )
                & ( r2_lattice3(sK4,X2,X3)
                  | r2_lattice3(sK4,X1,X3) )
                & m1_subset_1(X3,u1_struct_0(sK4)) )
            & ! [X4] :
                ( r2_hidden(k1_yellow_0(sK4,X4),X2)
                | k1_xboole_0 = X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X4) )
            & ! [X5] :
                ( ? [X6] :
                    ( k1_yellow_0(sK4,X6) = X5
                    & r1_yellow_0(sK4,X6)
                    & m1_subset_1(X6,k1_zfmisc_1(X1))
                    & v1_finset_1(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
            & ! [X7] :
                ( r1_yellow_0(sK4,X7)
                | k1_xboole_0 = X7
                | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X7) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(sK4,X2,X3)
                | ~ r2_lattice3(sK4,sK5,X3) )
              & ( r2_lattice3(sK4,X2,X3)
                | r2_lattice3(sK4,sK5,X3) )
              & m1_subset_1(X3,u1_struct_0(sK4)) )
          & ! [X4] :
              ( r2_hidden(k1_yellow_0(sK4,X4),X2)
              | k1_xboole_0 = X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(sK5))
              | ~ v1_finset_1(X4) )
          & ! [X5] :
              ( ? [X6] :
                  ( k1_yellow_0(sK4,X6) = X5
                  & r1_yellow_0(sK4,X6)
                  & m1_subset_1(X6,k1_zfmisc_1(sK5))
                  & v1_finset_1(X6) )
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
          & ! [X7] :
              ( r1_yellow_0(sK4,X7)
              | k1_xboole_0 = X7
              | ~ m1_subset_1(X7,k1_zfmisc_1(sK5))
              | ~ v1_finset_1(X7) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r2_lattice3(sK4,X2,X3)
              | ~ r2_lattice3(sK4,sK5,X3) )
            & ( r2_lattice3(sK4,X2,X3)
              | r2_lattice3(sK4,sK5,X3) )
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & ! [X4] :
            ( r2_hidden(k1_yellow_0(sK4,X4),X2)
            | k1_xboole_0 = X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(sK5))
            | ~ v1_finset_1(X4) )
        & ! [X5] :
            ( ? [X6] :
                ( k1_yellow_0(sK4,X6) = X5
                & r1_yellow_0(sK4,X6)
                & m1_subset_1(X6,k1_zfmisc_1(sK5))
                & v1_finset_1(X6) )
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
        & ! [X7] :
            ( r1_yellow_0(sK4,X7)
            | k1_xboole_0 = X7
            | ~ m1_subset_1(X7,k1_zfmisc_1(sK5))
            | ~ v1_finset_1(X7) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X3] :
          ( ( ~ r2_lattice3(sK4,sK6,X3)
            | ~ r2_lattice3(sK4,sK5,X3) )
          & ( r2_lattice3(sK4,sK6,X3)
            | r2_lattice3(sK4,sK5,X3) )
          & m1_subset_1(X3,u1_struct_0(sK4)) )
      & ! [X4] :
          ( r2_hidden(k1_yellow_0(sK4,X4),sK6)
          | k1_xboole_0 = X4
          | ~ m1_subset_1(X4,k1_zfmisc_1(sK5))
          | ~ v1_finset_1(X4) )
      & ! [X5] :
          ( ? [X6] :
              ( k1_yellow_0(sK4,X6) = X5
              & r1_yellow_0(sK4,X6)
              & m1_subset_1(X6,k1_zfmisc_1(sK5))
              & v1_finset_1(X6) )
          | ~ r2_hidden(X5,sK6)
          | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
      & ! [X7] :
          ( r1_yellow_0(sK4,X7)
          | k1_xboole_0 = X7
          | ~ m1_subset_1(X7,k1_zfmisc_1(sK5))
          | ~ v1_finset_1(X7) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ( ~ r2_lattice3(sK4,sK6,X3)
          | ~ r2_lattice3(sK4,sK5,X3) )
        & ( r2_lattice3(sK4,sK6,X3)
          | r2_lattice3(sK4,sK5,X3) )
        & m1_subset_1(X3,u1_struct_0(sK4)) )
   => ( ( ~ r2_lattice3(sK4,sK6,sK7)
        | ~ r2_lattice3(sK4,sK5,sK7) )
      & ( r2_lattice3(sK4,sK6,sK7)
        | r2_lattice3(sK4,sK5,sK7) )
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X5] :
      ( ? [X6] :
          ( k1_yellow_0(sK4,X6) = X5
          & r1_yellow_0(sK4,X6)
          & m1_subset_1(X6,k1_zfmisc_1(sK5))
          & v1_finset_1(X6) )
     => ( k1_yellow_0(sK4,sK8(X5)) = X5
        & r1_yellow_0(sK4,sK8(X5))
        & m1_subset_1(sK8(X5),k1_zfmisc_1(sK5))
        & v1_finset_1(sK8(X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | r2_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(X0,X6) = X5
                      & r1_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r1_yellow_0(X0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r2_lattice3(X0,X2,X7)
                    | ~ r2_lattice3(X0,X1,X7) )
                  & ( r2_lattice3(X0,X2,X7)
                    | r2_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r2_lattice3(X0,X2,X7)
                    | ~ r2_lattice3(X0,X1,X7) )
                  & ( r2_lattice3(X0,X2,X7)
                    | r2_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v4_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
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
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
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
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
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
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,negated_conjecture,(
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
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X3)
                      <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f460,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f459,f66])).

fof(f66,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f459,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f457,f75])).

fof(f75,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f457,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7)
    | r2_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f454,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK10(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK10(X0,X1,X2),X2)
                & r2_hidden(sK10(X0,X1,X2),X1)
                & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK10(X0,X1,X2),X2)
        & r2_hidden(sK10(X0,X1,X2),X1)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f454,plain,
    ( r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(subsumption_resolution,[],[f453,f66])).

fof(f453,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f452,f75])).

fof(f452,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7)
    | r2_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f439,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f439,plain,
    ( ~ m1_subset_1(sK10(sK4,sK5,sK7),u1_struct_0(sK4))
    | r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7) ),
    inference(subsumption_resolution,[],[f435,f75])).

fof(f435,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK10(sK4,sK5,sK7),u1_struct_0(sK4))
    | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7) ),
    inference(resolution,[],[f434,f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK4,k1_tarski(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r1_orders_2(sK4,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK4,k1_tarski(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r1_orders_2(sK4,X0,X1) ) ),
    inference(superposition,[],[f174,f81])).

fof(f81,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK4,k2_tarski(X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r1_orders_2(sK4,X2,X1) ) ),
    inference(resolution,[],[f173,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r2_lattice3(X2,k2_tarski(X3,X1),X0)
      | r1_orders_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_orders_2(X2,X1,X0)
        & r1_orders_2(X2,X3,X0) )
      | ~ r2_lattice3(X2,k2_tarski(X3,X1),X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X3,X0,X2] :
      ( ( r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ sP1(X1,X3,X0,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X3,X0,X2] :
      ( ( r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ sP1(X1,X3,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f88,f66])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP1(X1,X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & sP1(X1,X3,X0,X2)
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & sP0(X3,X1,X0,X2) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f22,f34,f33])).

fof(f33,plain,(
    ! [X3,X1,X0,X2] :
      ( ( r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ sP0(X3,X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f434,plain,
    ( r2_lattice3(sK4,k1_tarski(sK10(sK4,sK5,sK7)),sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,k1_tarski(sK10(sK4,sK5,sK7)),sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(resolution,[],[f362,f418])).

fof(f418,plain,
    ( r2_lattice3(sK4,k1_tarski(sK10(sK4,sK5,sK7)),k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(resolution,[],[f352,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK9(X0,X1,X2))
          & r2_lattice3(X1,X2,sK9(X0,X1,X2))
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r2_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X0,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X0) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK9(X0,X1,X2))
        & r2_lattice3(X1,X2,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r2_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X0,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X0) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f352,plain,
    ( sP2(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK4,k1_tarski(sK10(sK4,sK5,sK7)))
    | r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f282,f343])).

fof(f343,plain,
    ( m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4))
    | r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f188,f68])).

fof(f68,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f47])).

fof(f188,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X1))
      | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | r2_lattice3(sK4,sK5,sK7)
      | m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),X1) ) ),
    inference(resolution,[],[f133,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f133,plain,
    ( r2_hidden(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK6)
    | r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f128,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK5)
      | r2_hidden(k1_yellow_0(sK4,k1_tarski(X0)),sK6)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f120,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK5))
      | k1_xboole_0 = k1_tarski(X0)
      | r2_hidden(k1_yellow_0(sK4,k1_tarski(X0)),sK6) ) ),
    inference(resolution,[],[f74,f80])).

fof(f80,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f74,plain,(
    ! [X4] :
      ( ~ v1_finset_1(X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK5))
      | r2_hidden(k1_yellow_0(sK4,X4),sK6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    ! [X2] :
      ( r1_tarski(k1_tarski(sK10(sK4,X2,sK7)),X2)
      | r2_lattice3(sK4,X2,sK7) ) ),
    inference(resolution,[],[f124,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f124,plain,(
    ! [X2] :
      ( r2_hidden(sK10(sK4,X2,sK7),X2)
      | r2_lattice3(sK4,X2,sK7) ) ),
    inference(resolution,[],[f122,f75])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
      | r2_hidden(sK10(sK4,X0,X1),X0)
      | r2_lattice3(sK4,X0,X1) ) ),
    inference(resolution,[],[f102,f66])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK10(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f282,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | ~ m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4))
    | r2_lattice3(sK4,sK5,sK7)
    | sP2(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK4,k1_tarski(sK10(sK4,sK5,sK7))) ),
    inference(resolution,[],[f169,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1,k1_yellow_0(X1,X0))
      | sP2(k1_yellow_0(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | k1_yellow_0(X1,X0) != X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_yellow_0(X1,X0) = X2
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | k1_yellow_0(X1,X0) != X2 ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_yellow_0(X0,X1) = X2
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | k1_yellow_0(X0,X1) != X2 ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( k1_yellow_0(X0,X1) = X2
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f169,plain,(
    ! [X0] :
      ( sP3(k1_tarski(sK10(sK4,sK5,sK7)),sK4,X0)
      | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r2_lattice3(sK4,sK5,sK7) ) ),
    inference(resolution,[],[f134,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK4,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | sP3(X0,sK4,X1) ) ),
    inference(resolution,[],[f99,f66])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP3(X1,X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f25,f37,f36])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f134,plain,
    ( r1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))
    | r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f128,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK5)
      | r1_yellow_0(sK4,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f116,f110])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK5))
      | k1_xboole_0 = k1_tarski(X0)
      | r1_yellow_0(sK4,k1_tarski(X0)) ) ),
    inference(resolution,[],[f69,f80])).

fof(f69,plain,(
    ! [X7] :
      ( ~ v1_finset_1(X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK5))
      | r1_yellow_0(sK4,X7) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f362,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK4,X0,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))))
      | r2_lattice3(sK4,sK5,sK7)
      | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | r2_lattice3(sK4,X0,sK7) ) ),
    inference(subsumption_resolution,[],[f361,f343])).

fof(f361,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | r2_lattice3(sK4,sK5,sK7)
      | ~ r2_lattice3(sK4,X0,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))))
      | ~ m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4))
      | r2_lattice3(sK4,X0,sK7) ) ),
    inference(subsumption_resolution,[],[f360,f75])).

fof(f360,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | r2_lattice3(sK4,sK5,sK7)
      | ~ r2_lattice3(sK4,X0,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))))
      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
      | ~ m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4))
      | r2_lattice3(sK4,X0,sK7) ) ),
    inference(resolution,[],[f350,f296])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK4,X1,X2)
      | ~ r2_lattice3(sK4,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | r2_lattice3(sK4,X0,X2) ) ),
    inference(subsumption_resolution,[],[f295,f66])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK4,X0,X1)
      | ~ r1_orders_2(sK4,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | ~ l1_orders_2(sK4)
      | r2_lattice3(sK4,X0,X2) ) ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X3,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f350,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(subsumption_resolution,[],[f241,f343])).

fof(f241,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | ~ m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4))
    | r1_orders_2(sK4,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK7) ),
    inference(subsumption_resolution,[],[f238,f75])).

fof(f238,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4))
    | r1_orders_2(sK4,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK7) ),
    inference(resolution,[],[f210,f219])).

fof(f210,plain,
    ( r2_lattice3(sK4,k1_tarski(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))),sK7)
    | r2_lattice3(sK4,sK5,sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7)
    | r2_lattice3(sK4,k1_tarski(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))),sK7)
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(resolution,[],[f189,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK6)
      | r2_lattice3(sK4,X0,sK7)
      | r2_lattice3(sK4,sK5,sK7) ) ),
    inference(subsumption_resolution,[],[f148,f75])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
      | ~ r1_tarski(X0,sK6)
      | r2_lattice3(sK4,X0,sK7)
      | r2_lattice3(sK4,sK5,sK7) ) ),
    inference(resolution,[],[f147,f76])).

fof(f76,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK4,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK4))
      | ~ r1_tarski(X2,X0)
      | r2_lattice3(sK4,X2,X1) ) ),
    inference(resolution,[],[f91,f66])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f189,plain,
    ( r1_tarski(k1_tarski(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))),sK6)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(resolution,[],[f133,f108])).

fof(f1010,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK6,sK7) ),
    inference(subsumption_resolution,[],[f1009,f66])).

fof(f1009,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK6,sK7)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f1002,f75])).

fof(f1002,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r2_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f997,f103])).

fof(f997,plain,
    ( r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f996,f874])).

fof(f874,plain,
    ( r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f871,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f871,plain,
    ( m1_subset_1(sK8(sK10(sK4,sK6,sK7)),k1_zfmisc_1(sK5))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(global_subsumption,[],[f130,f461,f520])).

fof(f520,plain,
    ( m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f519,f66])).

fof(f519,plain,
    ( m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(superposition,[],[f106,f466])).

fof(f466,plain,
    ( sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7)))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f461,f248])).

fof(f248,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))) ),
    inference(subsumption_resolution,[],[f247,f66])).

fof(f247,plain,
    ( sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7)))
    | r2_lattice3(sK4,sK6,sK7)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f246,f75])).

fof(f246,plain,
    ( sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7)))
    | r2_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,
    ( sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7)))
    | r2_lattice3(sK4,sK6,sK7)
    | r2_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f129,f101])).

fof(f129,plain,
    ( ~ m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4))
    | sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7)))
    | r2_lattice3(sK4,sK6,sK7) ),
    inference(resolution,[],[f124,f73])).

fof(f73,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK6)
      | k1_yellow_0(sK4,sK8(X5)) = X5
      | ~ m1_subset_1(X5,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f130,plain,
    ( m1_subset_1(sK8(sK10(sK4,sK6,sK7)),k1_zfmisc_1(sK5))
    | r2_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4)) ),
    inference(resolution,[],[f124,f71])).

fof(f71,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK6)
      | m1_subset_1(sK8(X5),k1_zfmisc_1(sK5))
      | ~ m1_subset_1(X5,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f996,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7)
    | ~ r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5) ),
    inference(subsumption_resolution,[],[f991,f75])).

fof(f991,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7)
    | ~ r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5) ),
    inference(duplicate_literal_removal,[],[f989])).

fof(f989,plain,
    ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7)
    | ~ r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5)
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(resolution,[],[f933,f465])).

fof(f465,plain,(
    ! [X3] :
      ( r2_lattice3(sK4,X3,sK7)
      | ~ r1_tarski(X3,sK5)
      | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ) ),
    inference(subsumption_resolution,[],[f464,f75])).

fof(f464,plain,(
    ! [X3] :
      ( k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
      | ~ r1_tarski(X3,sK5)
      | r2_lattice3(sK4,X3,sK7) ) ),
    inference(resolution,[],[f460,f147])).

fof(f933,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK4,sK8(sK10(sK4,sK6,sK7)),X0)
      | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r1_orders_2(sK4,sK10(sK4,sK6,sK7),X0) ) ),
    inference(resolution,[],[f921,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f921,plain,
    ( sP2(sK10(sK4,sK6,sK7),sK4,sK8(sK10(sK4,sK6,sK7)))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f920,f461])).

fof(f920,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | sP2(sK10(sK4,sK6,sK7),sK4,sK8(sK10(sK4,sK6,sK7)))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(subsumption_resolution,[],[f917,f520])).

fof(f917,plain,
    ( ~ m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4))
    | r2_lattice3(sK4,sK6,sK7)
    | sP2(sK10(sK4,sK6,sK7),sK4,sK8(sK10(sK4,sK6,sK7)))
    | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) ),
    inference(superposition,[],[f272,f466])).

fof(f272,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))),u1_struct_0(sK4))
    | r2_lattice3(sK4,sK6,sK7)
    | sP2(k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))),sK4,sK8(sK10(sK4,sK6,sK7))) ),
    inference(resolution,[],[f271,f112])).

fof(f271,plain,(
    ! [X0] :
      ( sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r2_lattice3(sK4,sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f270,f66])).

fof(f270,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0)
      | r2_lattice3(sK4,sK6,sK7)
      | ~ l1_orders_2(sK4) ) ),
    inference(subsumption_resolution,[],[f269,f75])).

fof(f269,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0)
      | r2_lattice3(sK4,sK6,sK7)
      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
      | ~ l1_orders_2(sK4) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0)
      | r2_lattice3(sK4,sK6,sK7)
      | r2_lattice3(sK4,sK6,sK7)
      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
      | ~ l1_orders_2(sK4) ) ),
    inference(resolution,[],[f145,f101])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0)
      | r2_lattice3(sK4,sK6,sK7) ) ),
    inference(resolution,[],[f118,f124])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK6)
      | sP3(sK8(X1),sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X5] :
      ( r1_yellow_0(sK4,sK8(X5))
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (26374)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (26366)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (26355)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (26364)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (26360)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (26365)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (26362)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (26369)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (26377)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (26378)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.53  % (26370)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.53  % (26357)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  % (26382)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (26384)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (26358)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (26367)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (26381)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (26359)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.55  % (26356)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.55  % (26380)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.55  % (26376)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.55  % (26361)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.55  % (26363)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.55  % (26375)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.56  % (26368)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.46/0.56  % (26383)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.56  % (26372)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.56  % (26373)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.57  % (26379)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.57  % (26371)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.45/0.69  % (26362)Refutation found. Thanks to Tanya!
% 2.45/0.69  % SZS status Theorem for theBenchmark
% 2.45/0.69  % SZS output start Proof for theBenchmark
% 2.45/0.69  fof(f1027,plain,(
% 2.45/0.69    $false),
% 2.45/0.69    inference(subsumption_resolution,[],[f1013,f78])).
% 2.45/0.69  fof(f78,plain,(
% 2.45/0.69    v1_xboole_0(k1_xboole_0)),
% 2.45/0.69    inference(cnf_transformation,[],[f1])).
% 2.45/0.69  fof(f1,axiom,(
% 2.45/0.69    v1_xboole_0(k1_xboole_0)),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.45/0.69  fof(f1013,plain,(
% 2.45/0.69    ~v1_xboole_0(k1_xboole_0)),
% 2.45/0.69    inference(superposition,[],[f79,f1011])).
% 2.45/0.69  fof(f1011,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f1010,f461])).
% 2.45/0.69  fof(f461,plain,(
% 2.45/0.69    ~r2_lattice3(sK4,sK6,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f460,f77])).
% 2.45/0.69  fof(f77,plain,(
% 2.45/0.69    ~r2_lattice3(sK4,sK5,sK7) | ~r2_lattice3(sK4,sK6,sK7)),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f47,plain,(
% 2.45/0.69    ((((~r2_lattice3(sK4,sK6,sK7) | ~r2_lattice3(sK4,sK5,sK7)) & (r2_lattice3(sK4,sK6,sK7) | r2_lattice3(sK4,sK5,sK7)) & m1_subset_1(sK7,u1_struct_0(sK4))) & ! [X4] : (r2_hidden(k1_yellow_0(sK4,X4),sK6) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK5)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK4,sK8(X5)) = X5 & r1_yellow_0(sK4,sK8(X5)) & m1_subset_1(sK8(X5),k1_zfmisc_1(sK5)) & v1_finset_1(sK8(X5))) | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,u1_struct_0(sK4))) & ! [X7] : (r1_yellow_0(sK4,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK5)) | ~v1_finset_1(X7)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v4_orders_2(sK4)),
% 2.45/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f41,f46,f45,f44,f43,f42])).
% 2.45/0.69  fof(f42,plain,(
% 2.45/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK4,X2,X3) | ~r2_lattice3(sK4,X1,X3)) & (r2_lattice3(sK4,X2,X3) | r2_lattice3(sK4,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK4))) & ! [X4] : (r2_hidden(k1_yellow_0(sK4,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK4,X6) = X5 & r1_yellow_0(sK4,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK4))) & ! [X7] : (r1_yellow_0(sK4,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v4_orders_2(sK4))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f43,plain,(
% 2.45/0.69    ? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK4,X2,X3) | ~r2_lattice3(sK4,X1,X3)) & (r2_lattice3(sK4,X2,X3) | r2_lattice3(sK4,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK4))) & ! [X4] : (r2_hidden(k1_yellow_0(sK4,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK4,X6) = X5 & r1_yellow_0(sK4,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK4))) & ! [X7] : (r1_yellow_0(sK4,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X2] : (? [X3] : ((~r2_lattice3(sK4,X2,X3) | ~r2_lattice3(sK4,sK5,X3)) & (r2_lattice3(sK4,X2,X3) | r2_lattice3(sK4,sK5,X3)) & m1_subset_1(X3,u1_struct_0(sK4))) & ! [X4] : (r2_hidden(k1_yellow_0(sK4,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK5)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK4,X6) = X5 & r1_yellow_0(sK4,X6) & m1_subset_1(X6,k1_zfmisc_1(sK5)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK4))) & ! [X7] : (r1_yellow_0(sK4,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK5)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f44,plain,(
% 2.45/0.69    ? [X2] : (? [X3] : ((~r2_lattice3(sK4,X2,X3) | ~r2_lattice3(sK4,sK5,X3)) & (r2_lattice3(sK4,X2,X3) | r2_lattice3(sK4,sK5,X3)) & m1_subset_1(X3,u1_struct_0(sK4))) & ! [X4] : (r2_hidden(k1_yellow_0(sK4,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK5)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK4,X6) = X5 & r1_yellow_0(sK4,X6) & m1_subset_1(X6,k1_zfmisc_1(sK5)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK4))) & ! [X7] : (r1_yellow_0(sK4,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK5)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X3] : ((~r2_lattice3(sK4,sK6,X3) | ~r2_lattice3(sK4,sK5,X3)) & (r2_lattice3(sK4,sK6,X3) | r2_lattice3(sK4,sK5,X3)) & m1_subset_1(X3,u1_struct_0(sK4))) & ! [X4] : (r2_hidden(k1_yellow_0(sK4,X4),sK6) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK5)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK4,X6) = X5 & r1_yellow_0(sK4,X6) & m1_subset_1(X6,k1_zfmisc_1(sK5)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,u1_struct_0(sK4))) & ! [X7] : (r1_yellow_0(sK4,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK5)) | ~v1_finset_1(X7)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f45,plain,(
% 2.45/0.69    ? [X3] : ((~r2_lattice3(sK4,sK6,X3) | ~r2_lattice3(sK4,sK5,X3)) & (r2_lattice3(sK4,sK6,X3) | r2_lattice3(sK4,sK5,X3)) & m1_subset_1(X3,u1_struct_0(sK4))) => ((~r2_lattice3(sK4,sK6,sK7) | ~r2_lattice3(sK4,sK5,sK7)) & (r2_lattice3(sK4,sK6,sK7) | r2_lattice3(sK4,sK5,sK7)) & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f46,plain,(
% 2.45/0.69    ! [X5] : (? [X6] : (k1_yellow_0(sK4,X6) = X5 & r1_yellow_0(sK4,X6) & m1_subset_1(X6,k1_zfmisc_1(sK5)) & v1_finset_1(X6)) => (k1_yellow_0(sK4,sK8(X5)) = X5 & r1_yellow_0(sK4,sK8(X5)) & m1_subset_1(sK8(X5),k1_zfmisc_1(sK5)) & v1_finset_1(sK8(X5))))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f41,plain,(
% 2.45/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 2.45/0.69    inference(rectify,[],[f40])).
% 2.45/0.69  fof(f40,plain,(
% 2.45/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 2.45/0.69    inference(flattening,[],[f39])).
% 2.45/0.69  fof(f39,plain,(
% 2.45/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 2.45/0.69    inference(nnf_transformation,[],[f20])).
% 2.45/0.69  fof(f20,plain,(
% 2.45/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 2.45/0.69    inference(flattening,[],[f19])).
% 2.45/0.69  fof(f19,plain,(
% 2.45/0.69    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 2.45/0.69    inference(ennf_transformation,[],[f18])).
% 2.45/0.69  fof(f18,plain,(
% 2.45/0.69    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.45/0.69    inference(pure_predicate_removal,[],[f17])).
% 2.45/0.69  fof(f17,plain,(
% 2.45/0.69    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.45/0.69    inference(pure_predicate_removal,[],[f16])).
% 2.45/0.69  fof(f16,plain,(
% 2.45/0.69    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.45/0.69    inference(rectify,[],[f15])).
% 2.45/0.69  fof(f15,negated_conjecture,(
% 2.45/0.69    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 2.45/0.69    inference(negated_conjecture,[],[f14])).
% 2.45/0.69  fof(f14,conjecture,(
% 2.45/0.69    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).
% 2.45/0.69  fof(f460,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f459,f66])).
% 2.45/0.69  fof(f66,plain,(
% 2.45/0.69    l1_orders_2(sK4)),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f459,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(subsumption_resolution,[],[f457,f75])).
% 2.45/0.69  fof(f75,plain,(
% 2.45/0.69    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f457,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f456])).
% 2.45/0.69  fof(f456,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | r2_lattice3(sK4,sK5,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(resolution,[],[f454,f103])).
% 2.45/0.69  fof(f103,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK10(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f62])).
% 2.45/0.69  fof(f62,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK10(X0,X1,X2),X2) & r2_hidden(sK10(X0,X1,X2),X1) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f60,f61])).
% 2.45/0.69  fof(f61,plain,(
% 2.45/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK10(X0,X1,X2),X2) & r2_hidden(sK10(X0,X1,X2),X1) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f60,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(rectify,[],[f59])).
% 2.45/0.69  fof(f59,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(nnf_transformation,[],[f27])).
% 2.45/0.69  fof(f27,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(flattening,[],[f26])).
% 2.45/0.69  fof(f26,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(ennf_transformation,[],[f8])).
% 2.45/0.69  fof(f8,axiom,(
% 2.45/0.69    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 2.45/0.69  fof(f454,plain,(
% 2.45/0.69    r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(subsumption_resolution,[],[f453,f66])).
% 2.45/0.69  fof(f453,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(subsumption_resolution,[],[f452,f75])).
% 2.45/0.69  fof(f452,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f449])).
% 2.45/0.69  fof(f449,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7) | r2_lattice3(sK4,sK5,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(resolution,[],[f439,f101])).
% 2.45/0.69  fof(f101,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f62])).
% 2.45/0.69  fof(f439,plain,(
% 2.45/0.69    ~m1_subset_1(sK10(sK4,sK5,sK7),u1_struct_0(sK4)) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7)),
% 2.45/0.69    inference(subsumption_resolution,[],[f435,f75])).
% 2.45/0.69  fof(f435,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK10(sK4,sK5,sK7),u1_struct_0(sK4)) | r1_orders_2(sK4,sK10(sK4,sK5,sK7),sK7)),
% 2.45/0.69    inference(resolution,[],[f434,f219])).
% 2.45/0.69  fof(f219,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~r2_lattice3(sK4,k1_tarski(X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,X0,X1)) )),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f218])).
% 2.45/0.69  fof(f218,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~r2_lattice3(sK4,k1_tarski(X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,X0,X1)) )),
% 2.45/0.69    inference(superposition,[],[f174,f81])).
% 2.45/0.69  fof(f81,plain,(
% 2.45/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f2])).
% 2.45/0.69  fof(f2,axiom,(
% 2.45/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.45/0.69  fof(f174,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~r2_lattice3(sK4,k2_tarski(X0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,X2,X1)) )),
% 2.45/0.69    inference(resolution,[],[f173,f83])).
% 2.45/0.69  fof(f83,plain,(
% 2.45/0.69    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | ~r2_lattice3(X2,k2_tarski(X3,X1),X0) | r1_orders_2(X2,X1,X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f49])).
% 2.45/0.69  fof(f49,plain,(
% 2.45/0.69    ! [X0,X1,X2,X3] : ((r1_orders_2(X2,X1,X0) & r1_orders_2(X2,X3,X0)) | ~r2_lattice3(X2,k2_tarski(X3,X1),X0) | ~sP1(X0,X1,X2,X3))),
% 2.45/0.69    inference(rectify,[],[f48])).
% 2.45/0.69  fof(f48,plain,(
% 2.45/0.69    ! [X1,X3,X0,X2] : ((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~sP1(X1,X3,X0,X2))),
% 2.45/0.69    inference(nnf_transformation,[],[f34])).
% 2.45/0.69  fof(f34,plain,(
% 2.45/0.69    ! [X1,X3,X0,X2] : ((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~sP1(X1,X3,X0,X2))),
% 2.45/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.45/0.69  fof(f173,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (sP1(X2,X0,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4))) )),
% 2.45/0.69    inference(resolution,[],[f88,f66])).
% 2.45/0.69  fof(f88,plain,(
% 2.45/0.69    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP1(X1,X3,X0,X2)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f35])).
% 2.45/0.69  fof(f35,plain,(
% 2.45/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & sP1(X1,X3,X0,X2) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & sP0(X3,X1,X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(definition_folding,[],[f22,f34,f33])).
% 2.45/0.69  fof(f33,plain,(
% 2.45/0.69    ! [X3,X1,X0,X2] : ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~sP0(X3,X1,X0,X2))),
% 2.45/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.45/0.69  fof(f22,plain,(
% 2.45/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & ((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(flattening,[],[f21])).
% 2.45/0.69  fof(f21,plain,(
% 2.45/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_lattice3(X0,k2_tarski(X2,X3),X1) | (~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) | (~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(ennf_transformation,[],[f12])).
% 2.45/0.69  fof(f12,axiom,(
% 2.45/0.69    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) => r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r2_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) => r1_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))))))))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).
% 2.45/0.69  fof(f434,plain,(
% 2.45/0.69    r2_lattice3(sK4,k1_tarski(sK10(sK4,sK5,sK7)),sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f433])).
% 2.45/0.69  fof(f433,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,k1_tarski(sK10(sK4,sK5,sK7)),sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(resolution,[],[f362,f418])).
% 2.45/0.69  fof(f418,plain,(
% 2.45/0.69    r2_lattice3(sK4,k1_tarski(sK10(sK4,sK5,sK7)),k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(resolution,[],[f352,f94])).
% 2.45/0.69  fof(f94,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_lattice3(X1,X2,X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f58])).
% 2.45/0.69  fof(f58,plain,(
% 2.45/0.69    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_orders_2(X1,X0,sK9(X0,X1,X2)) & r2_lattice3(X1,X2,sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) | ~r2_lattice3(X1,X2,X0)) & ((! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_lattice3(X1,X2,X0)) | ~sP2(X0,X1,X2)))),
% 2.45/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f56,f57])).
% 2.45/0.69  fof(f57,plain,(
% 2.45/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK9(X0,X1,X2)) & r2_lattice3(X1,X2,sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 2.45/0.69    introduced(choice_axiom,[])).
% 2.45/0.69  fof(f56,plain,(
% 2.45/0.69    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_lattice3(X1,X2,X0)) & ((! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_lattice3(X1,X2,X0)) | ~sP2(X0,X1,X2)))),
% 2.45/0.69    inference(rectify,[],[f55])).
% 2.45/0.69  fof(f55,plain,(
% 2.45/0.69    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 2.45/0.69    inference(flattening,[],[f54])).
% 2.45/0.69  fof(f54,plain,(
% 2.45/0.69    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 2.45/0.69    inference(nnf_transformation,[],[f36])).
% 2.45/0.69  fof(f36,plain,(
% 2.45/0.69    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)))),
% 2.45/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.45/0.69  fof(f352,plain,(
% 2.45/0.69    sP2(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK4,k1_tarski(sK10(sK4,sK5,sK7))) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f282,f343])).
% 2.45/0.69  fof(f343,plain,(
% 2.45/0.69    m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4)) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f188,f68])).
% 2.45/0.69  fof(f68,plain,(
% 2.45/0.69    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f188,plain,(
% 2.45/0.69    ( ! [X1] : (~m1_subset_1(sK6,k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),X1)) )),
% 2.45/0.69    inference(resolution,[],[f133,f111])).
% 2.45/0.69  fof(f111,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f32])).
% 2.45/0.69  fof(f32,plain,(
% 2.45/0.69    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.45/0.69    inference(flattening,[],[f31])).
% 2.45/0.69  fof(f31,plain,(
% 2.45/0.69    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.45/0.69    inference(ennf_transformation,[],[f6])).
% 2.45/0.69  fof(f6,axiom,(
% 2.45/0.69    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.45/0.69  fof(f133,plain,(
% 2.45/0.69    r2_hidden(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK6) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f128,f121])).
% 2.45/0.69  fof(f121,plain,(
% 2.45/0.69    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK5) | r2_hidden(k1_yellow_0(sK4,k1_tarski(X0)),sK6) | k1_xboole_0 = k1_tarski(X0)) )),
% 2.45/0.69    inference(resolution,[],[f120,f110])).
% 2.45/0.69  fof(f110,plain,(
% 2.45/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f64])).
% 2.45/0.69  fof(f64,plain,(
% 2.45/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.45/0.69    inference(nnf_transformation,[],[f5])).
% 2.45/0.69  fof(f5,axiom,(
% 2.45/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.45/0.69  fof(f120,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK5)) | k1_xboole_0 = k1_tarski(X0) | r2_hidden(k1_yellow_0(sK4,k1_tarski(X0)),sK6)) )),
% 2.45/0.69    inference(resolution,[],[f74,f80])).
% 2.45/0.69  fof(f80,plain,(
% 2.45/0.69    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 2.45/0.69    inference(cnf_transformation,[],[f7])).
% 2.45/0.69  fof(f7,axiom,(
% 2.45/0.69    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 2.45/0.69  fof(f74,plain,(
% 2.45/0.69    ( ! [X4] : (~v1_finset_1(X4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK5)) | r2_hidden(k1_yellow_0(sK4,X4),sK6)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f128,plain,(
% 2.45/0.69    ( ! [X2] : (r1_tarski(k1_tarski(sK10(sK4,X2,sK7)),X2) | r2_lattice3(sK4,X2,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f124,f108])).
% 2.45/0.69  fof(f108,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f63])).
% 2.45/0.69  fof(f63,plain,(
% 2.45/0.69    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.45/0.69    inference(nnf_transformation,[],[f4])).
% 2.45/0.69  fof(f4,axiom,(
% 2.45/0.69    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.45/0.69  fof(f124,plain,(
% 2.45/0.69    ( ! [X2] : (r2_hidden(sK10(sK4,X2,sK7),X2) | r2_lattice3(sK4,X2,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f122,f75])).
% 2.45/0.69  fof(f122,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK4)) | r2_hidden(sK10(sK4,X0,X1),X0) | r2_lattice3(sK4,X0,X1)) )),
% 2.45/0.69    inference(resolution,[],[f102,f66])).
% 2.45/0.69  fof(f102,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK10(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f62])).
% 2.45/0.69  fof(f282,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4)) | r2_lattice3(sK4,sK5,sK7) | sP2(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK4,k1_tarski(sK10(sK4,sK5,sK7)))),
% 2.45/0.69    inference(resolution,[],[f169,f112])).
% 2.45/0.69  fof(f112,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~sP3(X0,X1,k1_yellow_0(X1,X0)) | sP2(k1_yellow_0(X1,X0),X1,X0)) )),
% 2.45/0.69    inference(equality_resolution,[],[f92])).
% 2.45/0.69  fof(f92,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | k1_yellow_0(X1,X0) != X2 | ~sP3(X0,X1,X2)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f53])).
% 2.45/0.69  fof(f53,plain,(
% 2.45/0.69    ! [X0,X1,X2] : (((k1_yellow_0(X1,X0) = X2 | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | k1_yellow_0(X1,X0) != X2)) | ~sP3(X0,X1,X2))),
% 2.45/0.69    inference(rectify,[],[f52])).
% 2.45/0.69  fof(f52,plain,(
% 2.45/0.69    ! [X1,X0,X2] : (((k1_yellow_0(X0,X1) = X2 | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | k1_yellow_0(X0,X1) != X2)) | ~sP3(X1,X0,X2))),
% 2.45/0.69    inference(nnf_transformation,[],[f37])).
% 2.45/0.69  fof(f37,plain,(
% 2.45/0.69    ! [X1,X0,X2] : ((k1_yellow_0(X0,X1) = X2 <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 2.45/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.45/0.69  fof(f169,plain,(
% 2.45/0.69    ( ! [X0] : (sP3(k1_tarski(sK10(sK4,sK5,sK7)),sK4,X0) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r2_lattice3(sK4,sK5,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f134,f117])).
% 2.45/0.69  fof(f117,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~r1_yellow_0(sK4,X0) | ~m1_subset_1(X1,u1_struct_0(sK4)) | sP3(X0,sK4,X1)) )),
% 2.45/0.69    inference(resolution,[],[f99,f66])).
% 2.45/0.69  fof(f99,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f38])).
% 2.45/0.69  fof(f38,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : (sP3(X1,X0,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(definition_folding,[],[f25,f37,f36])).
% 2.45/0.69  fof(f25,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(flattening,[],[f24])).
% 2.45/0.69  fof(f24,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(ennf_transformation,[],[f9])).
% 2.45/0.69  fof(f9,axiom,(
% 2.45/0.69    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 2.45/0.69  fof(f134,plain,(
% 2.45/0.69    r1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f128,f119])).
% 2.45/0.69  fof(f119,plain,(
% 2.45/0.69    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK5) | r1_yellow_0(sK4,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 2.45/0.69    inference(resolution,[],[f116,f110])).
% 2.45/0.69  fof(f116,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK5)) | k1_xboole_0 = k1_tarski(X0) | r1_yellow_0(sK4,k1_tarski(X0))) )),
% 2.45/0.69    inference(resolution,[],[f69,f80])).
% 2.45/0.69  fof(f69,plain,(
% 2.45/0.69    ( ! [X7] : (~v1_finset_1(X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK5)) | r1_yellow_0(sK4,X7)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f362,plain,(
% 2.45/0.69    ( ! [X0] : (~r2_lattice3(sK4,X0,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,X0,sK7)) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f361,f343])).
% 2.45/0.69  fof(f361,plain,(
% 2.45/0.69    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | ~r2_lattice3(sK4,X0,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))) | ~m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4)) | r2_lattice3(sK4,X0,sK7)) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f360,f75])).
% 2.45/0.69  fof(f360,plain,(
% 2.45/0.69    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | ~r2_lattice3(sK4,X0,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4)) | r2_lattice3(sK4,X0,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f350,f296])).
% 2.45/0.69  fof(f296,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~r1_orders_2(sK4,X1,X2) | ~r2_lattice3(sK4,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | r2_lattice3(sK4,X0,X2)) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f295,f66])).
% 2.45/0.69  fof(f295,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~r2_lattice3(sK4,X0,X1) | ~r1_orders_2(sK4,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | r2_lattice3(sK4,X0,X2)) )),
% 2.45/0.69    inference(resolution,[],[f105,f65])).
% 2.45/0.69  fof(f65,plain,(
% 2.45/0.69    v4_orders_2(sK4)),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f105,plain,(
% 2.45/0.69    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~r2_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X3,X2)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f29])).
% 2.45/0.69  fof(f29,plain,(
% 2.45/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 2.45/0.69    inference(flattening,[],[f28])).
% 2.45/0.69  fof(f28,plain,(
% 2.45/0.69    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.45/0.69    inference(ennf_transformation,[],[f11])).
% 2.45/0.69  fof(f11,axiom,(
% 2.45/0.69    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).
% 2.45/0.69  fof(f350,plain,(
% 2.45/0.69    r1_orders_2(sK4,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(subsumption_resolution,[],[f241,f343])).
% 2.45/0.69  fof(f241,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4)) | r1_orders_2(sK4,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK7)),
% 2.45/0.69    inference(subsumption_resolution,[],[f238,f75])).
% 2.45/0.69  fof(f238,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),u1_struct_0(sK4)) | r1_orders_2(sK4,k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7))),sK7)),
% 2.45/0.69    inference(resolution,[],[f210,f219])).
% 2.45/0.69  fof(f210,plain,(
% 2.45/0.69    r2_lattice3(sK4,k1_tarski(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))),sK7) | r2_lattice3(sK4,sK5,sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f209])).
% 2.45/0.69  fof(f209,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7) | r2_lattice3(sK4,k1_tarski(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))),sK7) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(resolution,[],[f189,f150])).
% 2.45/0.69  fof(f150,plain,(
% 2.45/0.69    ( ! [X0] : (~r1_tarski(X0,sK6) | r2_lattice3(sK4,X0,sK7) | r2_lattice3(sK4,sK5,sK7)) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f148,f75])).
% 2.45/0.69  fof(f148,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(sK7,u1_struct_0(sK4)) | ~r1_tarski(X0,sK6) | r2_lattice3(sK4,X0,sK7) | r2_lattice3(sK4,sK5,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f147,f76])).
% 2.45/0.69  fof(f76,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK6,sK7) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f147,plain,(
% 2.45/0.69    ( ! [X2,X0,X1] : (~r2_lattice3(sK4,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~r1_tarski(X2,X0) | r2_lattice3(sK4,X2,X1)) )),
% 2.45/0.69    inference(resolution,[],[f91,f66])).
% 2.45/0.69  fof(f91,plain,(
% 2.45/0.69    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | r2_lattice3(X0,X1,X3)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f23])).
% 2.45/0.69  fof(f23,plain,(
% 2.45/0.69    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(ennf_transformation,[],[f13])).
% 2.45/0.69  fof(f13,axiom,(
% 2.45/0.69    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 2.45/0.69  fof(f189,plain,(
% 2.45/0.69    r1_tarski(k1_tarski(k1_yellow_0(sK4,k1_tarski(sK10(sK4,sK5,sK7)))),sK6) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK5,sK7)),
% 2.45/0.69    inference(resolution,[],[f133,f108])).
% 2.45/0.69  fof(f1010,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK6,sK7)),
% 2.45/0.69    inference(subsumption_resolution,[],[f1009,f66])).
% 2.45/0.69  fof(f1009,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK6,sK7) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(subsumption_resolution,[],[f1002,f75])).
% 2.45/0.69  fof(f1002,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r2_lattice3(sK4,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(resolution,[],[f997,f103])).
% 2.45/0.69  fof(f997,plain,(
% 2.45/0.69    r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f996,f874])).
% 2.45/0.69  fof(f874,plain,(
% 2.45/0.69    r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f871,f109])).
% 2.45/0.69  fof(f109,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f64])).
% 2.45/0.69  fof(f871,plain,(
% 2.45/0.69    m1_subset_1(sK8(sK10(sK4,sK6,sK7)),k1_zfmisc_1(sK5)) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(global_subsumption,[],[f130,f461,f520])).
% 2.45/0.69  fof(f520,plain,(
% 2.45/0.69    m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4)) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f519,f66])).
% 2.45/0.69  fof(f519,plain,(
% 2.45/0.69    m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4)) | ~l1_orders_2(sK4) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(superposition,[],[f106,f466])).
% 2.45/0.69  fof(f466,plain,(
% 2.45/0.69    sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f461,f248])).
% 2.45/0.69  fof(f248,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK6,sK7) | sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7)))),
% 2.45/0.69    inference(subsumption_resolution,[],[f247,f66])).
% 2.45/0.69  fof(f247,plain,(
% 2.45/0.69    sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))) | r2_lattice3(sK4,sK6,sK7) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(subsumption_resolution,[],[f246,f75])).
% 2.45/0.69  fof(f246,plain,(
% 2.45/0.69    sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))) | r2_lattice3(sK4,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f243])).
% 2.45/0.69  fof(f243,plain,(
% 2.45/0.69    sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))) | r2_lattice3(sK4,sK6,sK7) | r2_lattice3(sK4,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)),
% 2.45/0.69    inference(resolution,[],[f129,f101])).
% 2.45/0.69  fof(f129,plain,(
% 2.45/0.69    ~m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4)) | sK10(sK4,sK6,sK7) = k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))) | r2_lattice3(sK4,sK6,sK7)),
% 2.45/0.69    inference(resolution,[],[f124,f73])).
% 2.45/0.69  fof(f73,plain,(
% 2.45/0.69    ( ! [X5] : (~r2_hidden(X5,sK6) | k1_yellow_0(sK4,sK8(X5)) = X5 | ~m1_subset_1(X5,u1_struct_0(sK4))) )),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f106,plain,(
% 2.45/0.69    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f30])).
% 2.45/0.69  fof(f30,plain,(
% 2.45/0.69    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.45/0.69    inference(ennf_transformation,[],[f10])).
% 2.45/0.69  fof(f10,axiom,(
% 2.45/0.69    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 2.45/0.69  fof(f130,plain,(
% 2.45/0.69    m1_subset_1(sK8(sK10(sK4,sK6,sK7)),k1_zfmisc_1(sK5)) | r2_lattice3(sK4,sK6,sK7) | ~m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4))),
% 2.45/0.69    inference(resolution,[],[f124,f71])).
% 2.45/0.69  fof(f71,plain,(
% 2.45/0.69    ( ! [X5] : (~r2_hidden(X5,sK6) | m1_subset_1(sK8(X5),k1_zfmisc_1(sK5)) | ~m1_subset_1(X5,u1_struct_0(sK4))) )),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f996,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7) | ~r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5)),
% 2.45/0.69    inference(subsumption_resolution,[],[f991,f75])).
% 2.45/0.69  fof(f991,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7) | ~r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5)),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f989])).
% 2.45/0.69  fof(f989,plain,(
% 2.45/0.69    k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | r1_orders_2(sK4,sK10(sK4,sK6,sK7),sK7) | ~r1_tarski(sK8(sK10(sK4,sK6,sK7)),sK5) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(resolution,[],[f933,f465])).
% 2.45/0.69  fof(f465,plain,(
% 2.45/0.69    ( ! [X3] : (r2_lattice3(sK4,X3,sK7) | ~r1_tarski(X3,sK5) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f464,f75])).
% 2.45/0.69  fof(f464,plain,(
% 2.45/0.69    ( ! [X3] : (k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~r1_tarski(X3,sK5) | r2_lattice3(sK4,X3,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f460,f147])).
% 2.45/0.69  fof(f933,plain,(
% 2.45/0.69    ( ! [X0] : (~r2_lattice3(sK4,sK8(sK10(sK4,sK6,sK7)),X0) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,sK10(sK4,sK6,sK7),X0)) )),
% 2.45/0.69    inference(resolution,[],[f921,f95])).
% 2.45/0.69  fof(f95,plain,(
% 2.45/0.69    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4)) )),
% 2.45/0.69    inference(cnf_transformation,[],[f58])).
% 2.45/0.69  fof(f921,plain,(
% 2.45/0.69    sP2(sK10(sK4,sK6,sK7),sK4,sK8(sK10(sK4,sK6,sK7))) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f920,f461])).
% 2.45/0.69  fof(f920,plain,(
% 2.45/0.69    r2_lattice3(sK4,sK6,sK7) | sP2(sK10(sK4,sK6,sK7),sK4,sK8(sK10(sK4,sK6,sK7))) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(subsumption_resolution,[],[f917,f520])).
% 2.45/0.69  fof(f917,plain,(
% 2.45/0.69    ~m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4)) | r2_lattice3(sK4,sK6,sK7) | sP2(sK10(sK4,sK6,sK7),sK4,sK8(sK10(sK4,sK6,sK7))) | k1_xboole_0 = k1_tarski(sK10(sK4,sK5,sK7))),
% 2.45/0.69    inference(superposition,[],[f272,f466])).
% 2.45/0.69  fof(f272,plain,(
% 2.45/0.69    ~m1_subset_1(k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))),u1_struct_0(sK4)) | r2_lattice3(sK4,sK6,sK7) | sP2(k1_yellow_0(sK4,sK8(sK10(sK4,sK6,sK7))),sK4,sK8(sK10(sK4,sK6,sK7)))),
% 2.45/0.69    inference(resolution,[],[f271,f112])).
% 2.45/0.69  fof(f271,plain,(
% 2.45/0.69    ( ! [X0] : (sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r2_lattice3(sK4,sK6,sK7)) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f270,f66])).
% 2.45/0.69  fof(f270,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0) | r2_lattice3(sK4,sK6,sK7) | ~l1_orders_2(sK4)) )),
% 2.45/0.69    inference(subsumption_resolution,[],[f269,f75])).
% 2.45/0.69  fof(f269,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0) | r2_lattice3(sK4,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)) )),
% 2.45/0.69    inference(duplicate_literal_removal,[],[f266])).
% 2.45/0.69  fof(f266,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0) | r2_lattice3(sK4,sK6,sK7) | r2_lattice3(sK4,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~l1_orders_2(sK4)) )),
% 2.45/0.69    inference(resolution,[],[f145,f101])).
% 2.45/0.69  fof(f145,plain,(
% 2.45/0.69    ( ! [X0] : (~m1_subset_1(sK10(sK4,sK6,sK7),u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | sP3(sK8(sK10(sK4,sK6,sK7)),sK4,X0) | r2_lattice3(sK4,sK6,sK7)) )),
% 2.45/0.69    inference(resolution,[],[f118,f124])).
% 2.45/0.69  fof(f118,plain,(
% 2.45/0.69    ( ! [X0,X1] : (~r2_hidden(X1,sK6) | sP3(sK8(X1),sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK4))) )),
% 2.45/0.69    inference(resolution,[],[f117,f72])).
% 2.45/0.69  fof(f72,plain,(
% 2.45/0.69    ( ! [X5] : (r1_yellow_0(sK4,sK8(X5)) | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,u1_struct_0(sK4))) )),
% 2.45/0.69    inference(cnf_transformation,[],[f47])).
% 2.45/0.69  fof(f79,plain,(
% 2.45/0.69    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.45/0.69    inference(cnf_transformation,[],[f3])).
% 2.45/0.69  fof(f3,axiom,(
% 2.45/0.69    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.45/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.45/0.69  % SZS output end Proof for theBenchmark
% 2.45/0.69  % (26362)------------------------------
% 2.45/0.69  % (26362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.69  % (26362)Termination reason: Refutation
% 2.45/0.69  
% 2.45/0.69  % (26362)Memory used [KB]: 8187
% 2.45/0.69  % (26362)Time elapsed: 0.255 s
% 2.45/0.69  % (26362)------------------------------
% 2.45/0.69  % (26362)------------------------------
% 2.45/0.69  % (26354)Success in time 0.333 s
%------------------------------------------------------------------------------

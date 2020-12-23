%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1586+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:58 EST 2020

% Result     : Theorem 15.12s
% Output     : CNFRefutation 15.12s
% Verified   : 
% Statistics : Number of formulae       :  313 (15363 expanded)
%              Number of clauses        :  215 (3623 expanded)
%              Number of leaves         :   21 (4532 expanded)
%              Depth                    :   38
%              Number of atoms          : 1684 (139468 expanded)
%              Number of equality atoms :  517 (16073 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              & r2_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X3,X4)
                | ~ r2_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X3,X4)
                | ~ r2_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X5,X6)
                & r2_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X5,X6)
          & r2_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X5,sK2(X1,X2,X5))
        & r2_lattice3(X1,X2,sK2(X1,X2,X5))
        & m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X3,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK1(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,sK1(X0,X1,X2),X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_lattice3(X1,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK1(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,sK1(X0,X1,X2),X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,sK1(X0,X1,X2))
          & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,X5,sK2(X1,X2,X5))
              & r2_lattice3(X1,X2,sK2(X1,X2,X5))
              & m1_subset_1(sK2(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_lattice3(X1,X2,sK1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                    & r1_yellow_0(X0,X2) )
                 => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                    & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
            | ~ r1_yellow_0(X1,X2) )
          & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
          & r1_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( k1_yellow_0(X0,sK8) != k1_yellow_0(X1,sK8)
          | ~ r1_yellow_0(X1,sK8) )
        & r2_hidden(k1_yellow_0(X0,sK8),u1_struct_0(X1))
        & r1_yellow_0(X0,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k1_yellow_0(sK7,X2) != k1_yellow_0(X0,X2)
              | ~ r1_yellow_0(sK7,X2) )
            & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(sK7))
            & r1_yellow_0(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
        & m1_yellow_0(sK7,X0)
        & v4_yellow_0(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                  | ~ r1_yellow_0(X1,X2) )
                & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                & r1_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(sK6,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(sK6,X2),u1_struct_0(X1))
              & r1_yellow_0(sK6,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK6)
          & v4_yellow_0(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK6)
      & v4_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( k1_yellow_0(sK6,sK8) != k1_yellow_0(sK7,sK8)
      | ~ r1_yellow_0(sK7,sK8) )
    & r2_hidden(k1_yellow_0(sK6,sK8),u1_struct_0(sK7))
    & r1_yellow_0(sK6,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & m1_yellow_0(sK7,sK6)
    & v4_yellow_0(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_orders_2(sK6)
    & v4_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f40,f60,f59,f58])).

fof(f100,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X1,X2,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X0,X2,X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f99,plain,(
    m1_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
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
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
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
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,sK1(X0,X1,X2),X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    r2_hidden(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f61])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f107,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X4,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    r1_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( sP0(X2,X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f41])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( sP0(X2,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X2,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( sP0(X4,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK4(X0,X1),X0,X1)
        & ! [X5] :
            ( r1_orders_2(X0,sK4(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( sP0(sK4(X0,X1),X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,sK4(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f49,f51,f50])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK4(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X3 = X4
                   => ( ( r2_lattice3(X0,X2,X3)
                       => r2_lattice3(X1,X2,X4) )
                      & ( r1_lattice3(X0,X2,X3)
                       => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f98,plain,(
    v4_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f109,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f108])).

fof(f103,plain,
    ( k1_yellow_0(sK6,sK8) != k1_yellow_0(sK7,sK8)
    | ~ r1_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f61])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK1(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( r2_lattice3(X0,X1,sK1(X2,X0,X1))
    | sP0(X2,X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7532,plain,
    ( r2_lattice3(X0,X1,sK1(X2,X0,X1)) = iProver_top
    | sP0(X2,X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7531,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_7525,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_36,negated_conjecture,
    ( m1_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_688,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X3)
    | sK7 != X0
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_36])).

cnf(c_689,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_39,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_lattice3(sK6,X0,X1)
    | ~ r2_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_41,c_39,c_38])).

cnf(c_694,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_693])).

cnf(c_24,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | sK7 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_664,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_660,c_41,c_39,c_38])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_704,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_694,c_665])).

cnf(c_7521,plain,
    ( r2_lattice3(sK7,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_10544,plain,
    ( r2_lattice3(sK7,sK8,X0) != iProver_top
    | r2_lattice3(sK6,sK8,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7525,c_7521])).

cnf(c_10549,plain,
    ( r2_lattice3(sK7,sK8,sK1(X0,sK7,X1)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) = iProver_top
    | sP0(X0,sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7531,c_10544])).

cnf(c_10968,plain,
    ( r2_lattice3(sK6,sK8,sK1(X0,sK7,sK8)) = iProver_top
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7532,c_10549])).

cnf(c_16,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_808,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_809,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK5(sK6,X0,X1),u1_struct_0(sK6))
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_7514,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK5(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_829,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_39])).

cnf(c_830,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r2_lattice3(sK6,X0,sK5(sK6,X0,X1))
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_7513,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,sK5(sK6,X0,X1)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_7522,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_7980,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | m1_subset_1(sK1(X0,sK7,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7531,c_7522])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK1(X3,X0,X1),X2)
    | sP0(X3,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7533,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,sK1(X3,X0,X1),X2) = iProver_top
    | sP0(X3,X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_584,plain,
    ( m1_subset_1(X0,X1)
    | k1_yellow_0(sK6,sK8) != X0
    | u1_struct_0(sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_585,plain,
    ( m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_7523,plain,
    ( m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_25,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_716,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | sK7 != X0
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_717,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_39,c_665])).

cnf(c_722,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_732,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_722,c_665])).

cnf(c_7520,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_9702,plain,
    ( r1_orders_2(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r1_orders_2(sK6,X0,k1_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7523,c_7520])).

cnf(c_9810,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r1_orders_2(sK6,sK1(X1,sK7,X0),k1_yellow_0(sK6,sK8)) = iProver_top
    | sP0(X1,sK7,X0) = iProver_top
    | m1_subset_1(sK1(X1,sK7,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7533,c_9702])).

cnf(c_586,plain,
    ( m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_10003,plain,
    ( m1_subset_1(sK1(X1,sK7,X0),u1_struct_0(sK7)) != iProver_top
    | sP0(X1,sK7,X0) = iProver_top
    | r1_orders_2(sK6,sK1(X1,sK7,X0),k1_yellow_0(sK6,sK8)) = iProver_top
    | r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9810,c_586])).

cnf(c_10004,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r1_orders_2(sK6,sK1(X1,sK7,X0),k1_yellow_0(sK6,sK8)) = iProver_top
    | sP0(X1,sK7,X0) = iProver_top
    | m1_subset_1(sK1(X1,sK7,X0),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10003])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_19,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_19])).

cnf(c_246,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_769,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_246,c_39])).

cnf(c_770,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_7517,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_22,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_473,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_40])).

cnf(c_474,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X1,X2)
    | r1_orders_2(sK6,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_orders_2(sK6,X0,X2)
    | ~ r1_orders_2(sK6,X1,X2)
    | ~ r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_39])).

cnf(c_477,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X2,X0)
    | r1_orders_2(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_7524,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X0) != iProver_top
    | r1_orders_2(sK6,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_8230,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X1) = iProver_top
    | r1_orders_2(sK6,X2,k1_yellow_0(sK6,X0)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7517,c_7524])).

cnf(c_799,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_800,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_801,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_12131,plain,
    ( m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | r1_orders_2(sK6,X2,k1_yellow_0(sK6,X0)) != iProver_top
    | r1_orders_2(sK6,X2,X1) = iProver_top
    | r2_lattice3(sK6,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8230,c_801])).

cnf(c_12132,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X1) = iProver_top
    | r1_orders_2(sK6,X2,k1_yellow_0(sK6,X0)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12131])).

cnf(c_12140,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,X1) != iProver_top
    | r1_orders_2(sK6,sK1(X2,sK7,X0),X1) = iProver_top
    | sP0(X2,sK7,X0) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10004,c_12132])).

cnf(c_34,negated_conjecture,
    ( r1_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_49,plain,
    ( r1_yellow_0(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36205,plain,
    ( sP0(X2,sK7,X0) = iProver_top
    | r1_orders_2(sK6,sK1(X2,sK7,X0),X1) = iProver_top
    | r2_lattice3(sK6,sK8,X1) != iProver_top
    | r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12140,c_49])).

cnf(c_36206,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,X1) != iProver_top
    | r1_orders_2(sK6,sK1(X2,sK7,X0),X1) = iProver_top
    | sP0(X2,sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36205])).

cnf(c_7526,plain,
    ( r1_yellow_0(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK4(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_895,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK4(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_39])).

cnf(c_896,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r1_orders_2(sK6,sK4(sK6,X0),X1)
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_7509,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,sK4(sK6,X0),X1) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_850,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_39])).

cnf(c_851,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X1,sK5(sK6,X0,X1))
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k1_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_7512,plain,
    ( k1_yellow_0(sK6,X0) = X1
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X1,sK5(sK6,X0,X1)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_8171,plain,
    ( k1_yellow_0(sK6,X0) = sK4(sK6,X1)
    | r2_lattice3(sK6,X1,sK5(sK6,X0,sK4(sK6,X1))) != iProver_top
    | r2_lattice3(sK6,X0,sK4(sK6,X1)) != iProver_top
    | r1_yellow_0(sK6,X1) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(sK5(sK6,X0,sK4(sK6,X1)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK6,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7509,c_7512])).

cnf(c_12846,plain,
    ( k1_yellow_0(sK6,X0) = sK4(sK6,X0)
    | r2_lattice3(sK6,X0,sK4(sK6,X0)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(sK5(sK6,X0,sK4(sK6,X0)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7513,c_8171])).

cnf(c_13,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_871,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_39])).

cnf(c_872,plain,
    ( ~ r1_yellow_0(sK6,X0)
    | m1_subset_1(sK4(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_873,plain,
    ( r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(sK4(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,sK4(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_883,plain,
    ( r2_lattice3(X0,X1,sK4(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_39])).

cnf(c_884,plain,
    ( r2_lattice3(sK6,X0,sK4(sK6,X0))
    | ~ r1_yellow_0(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_885,plain,
    ( r2_lattice3(sK6,X0,sK4(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_12851,plain,
    ( m1_subset_1(sK5(sK6,X0,sK4(sK6,X0)),u1_struct_0(sK6)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | k1_yellow_0(sK6,X0) = sK4(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12846,c_873,c_885])).

cnf(c_12852,plain,
    ( k1_yellow_0(sK6,X0) = sK4(sK6,X0)
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(sK5(sK6,X0,sK4(sK6,X0)),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12851])).

cnf(c_12857,plain,
    ( k1_yellow_0(sK6,X0) = sK4(sK6,X0)
    | r2_lattice3(sK6,X0,sK4(sK6,X0)) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(sK4(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7514,c_12852])).

cnf(c_12965,plain,
    ( r1_yellow_0(sK6,X0) != iProver_top
    | k1_yellow_0(sK6,X0) = sK4(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12857,c_873,c_885])).

cnf(c_12966,plain,
    ( k1_yellow_0(sK6,X0) = sK4(sK6,X0)
    | r1_yellow_0(sK6,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12965])).

cnf(c_12971,plain,
    ( k1_yellow_0(sK6,sK8) = sK4(sK6,sK8) ),
    inference(superposition,[status(thm)],[c_7526,c_12966])).

cnf(c_36211,plain,
    ( r2_lattice3(sK7,X0,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,X1) != iProver_top
    | r1_orders_2(sK6,sK1(X2,sK7,X0),X1) = iProver_top
    | sP0(X2,sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36206,c_12971])).

cnf(c_36215,plain,
    ( r2_lattice3(sK7,X0,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,X1) != iProver_top
    | r1_orders_2(sK6,sK1(X2,sK7,X0),X1) = iProver_top
    | sP0(X2,sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X2,sK7,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7531,c_36211])).

cnf(c_36490,plain,
    ( r2_lattice3(sK7,X0,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,X1) != iProver_top
    | r1_orders_2(sK6,sK1(X2,sK7,X0),X1) = iProver_top
    | sP0(X2,sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7980,c_36215])).

cnf(c_39139,plain,
    ( sK1(X0,sK7,X1) = k1_yellow_0(sK6,X2)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,X2,sK1(X0,sK7,X1)) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK6,X2,sK1(X0,sK7,X1))) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r1_yellow_0(sK6,X2) != iProver_top
    | m1_subset_1(sK5(sK6,X2,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X0,sK7,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36490,c_7512])).

cnf(c_40589,plain,
    ( m1_subset_1(sK5(sK6,X2,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top
    | r1_yellow_0(sK6,X2) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK6,X2,sK1(X0,sK7,X1))) != iProver_top
    | r2_lattice3(sK6,X2,sK1(X0,sK7,X1)) != iProver_top
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | sK1(X0,sK7,X1) = k1_yellow_0(sK6,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39139,c_7980])).

cnf(c_40590,plain,
    ( sK1(X0,sK7,X1) = k1_yellow_0(sK6,X2)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,X2,sK1(X0,sK7,X1)) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK6,X2,sK1(X0,sK7,X1))) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r1_yellow_0(sK6,X2) != iProver_top
    | m1_subset_1(sK5(sK6,X2,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_40589])).

cnf(c_40595,plain,
    ( sK1(X0,sK7,X1) = k1_yellow_0(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top
    | m1_subset_1(sK5(sK6,sK8,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X0,sK7,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7513,c_40590])).

cnf(c_40596,plain,
    ( sK1(X0,sK7,X1) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top
    | m1_subset_1(sK5(sK6,sK8,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(X0,sK7,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40595,c_12971])).

cnf(c_40668,plain,
    ( m1_subset_1(sK5(sK6,sK8,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top
    | sK1(X0,sK7,X1) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40596,c_49,c_7980])).

cnf(c_40669,plain,
    ( sK1(X0,sK7,X1) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | m1_subset_1(sK5(sK6,sK8,sK1(X0,sK7,X1)),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_40668])).

cnf(c_40674,plain,
    ( sK1(X0,sK7,X1) = k1_yellow_0(sK6,sK8)
    | sK1(X0,sK7,X1) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top
    | m1_subset_1(sK1(X0,sK7,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7514,c_40669])).

cnf(c_40675,plain,
    ( sK1(X0,sK7,X1) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top
    | m1_subset_1(sK1(X0,sK7,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40674,c_12971])).

cnf(c_40680,plain,
    ( sK1(X0,sK7,X1) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X1,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK1(X0,sK7,X1)) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40675,c_49,c_7980])).

cnf(c_40686,plain,
    ( sK1(X0,sK7,sK8) = sK4(sK6,sK8)
    | r2_lattice3(sK7,sK8,sK4(sK6,sK8)) != iProver_top
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_10968,c_40680])).

cnf(c_18,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_238,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_239,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_787,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_39])).

cnf(c_788,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0))
    | ~ r1_yellow_0(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_7516,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_27,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_37,negated_conjecture,
    ( v4_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_506,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X1,X2)
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | sK7 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_507,plain,
    ( r2_lattice3(sK7,X0,X1)
    | ~ r2_lattice3(sK6,X0,X1)
    | ~ m1_yellow_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_lattice3(sK7,X0,X1)
    | ~ r2_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_41,c_39,c_38,c_36])).

cnf(c_512,plain,
    ( r2_lattice3(sK7,X0,X1)
    | ~ r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_746,plain,
    ( r2_lattice3(sK7,X0,X1)
    | ~ r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_665,c_512])).

cnf(c_7519,plain,
    ( r2_lattice3(sK7,X0,X1) = iProver_top
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_9371,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7516,c_7519])).

cnf(c_9545,plain,
    ( r2_lattice3(sK7,sK8,k1_yellow_0(sK6,sK8)) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7523,c_9371])).

cnf(c_4233,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0))
    | sK8 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_788])).

cnf(c_4234,plain,
    ( r2_lattice3(sK6,sK8,k1_yellow_0(sK6,sK8)) ),
    inference(unflattening,[status(thm)],[c_4233])).

cnf(c_4235,plain,
    ( r2_lattice3(sK6,sK8,k1_yellow_0(sK6,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4234])).

cnf(c_7733,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8))
    | ~ r2_lattice3(sK6,X0,k1_yellow_0(sK6,sK8))
    | ~ m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_7921,plain,
    ( r2_lattice3(sK7,sK8,k1_yellow_0(sK6,sK8))
    | ~ r2_lattice3(sK6,sK8,k1_yellow_0(sK6,sK8))
    | ~ m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7733])).

cnf(c_7922,plain,
    ( r2_lattice3(sK7,sK8,k1_yellow_0(sK6,sK8)) = iProver_top
    | r2_lattice3(sK6,sK8,k1_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7921])).

cnf(c_9548,plain,
    ( r2_lattice3(sK7,sK8,k1_yellow_0(sK6,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9545,c_586,c_4235,c_7922])).

cnf(c_12977,plain,
    ( r2_lattice3(sK7,sK8,sK4(sK6,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12971,c_9548])).

cnf(c_41433,plain,
    ( sK1(X0,sK7,sK8) = sK4(sK6,sK8)
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40686,c_12977])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_677,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_678,plain,
    ( l1_orders_2(sK7)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_680,plain,
    ( l1_orders_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_39])).

cnf(c_1165,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_680])).

cnf(c_1166,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK7,X0,sK3(sK7,X0,X1))
    | ~ sP0(X1,sK7,X0)
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1165])).

cnf(c_7493,plain,
    ( r2_lattice3(sK7,X0,X1) != iProver_top
    | r2_lattice3(sK7,X0,sK3(sK7,X0,X1)) = iProver_top
    | sP0(X1,sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1144,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_680])).

cnf(c_1145,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | ~ sP0(X1,sK7,X0)
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK3(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1144])).

cnf(c_7494,plain,
    ( r2_lattice3(sK7,X0,X1) != iProver_top
    | sP0(X1,sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_10553,plain,
    ( r2_lattice3(sK7,X0,X1) != iProver_top
    | r2_lattice3(sK7,sK8,sK3(sK7,X0,X1)) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,X0,X1)) = iProver_top
    | sP0(X1,sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7494,c_10544])).

cnf(c_17519,plain,
    ( r2_lattice3(sK7,sK8,X0) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,sK8,X0)) = iProver_top
    | sP0(X0,sK7,sK8) != iProver_top
    | r1_yellow_0(sK7,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7493,c_10553])).

cnf(c_1027,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_680])).

cnf(c_1028,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | ~ r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0,X1),u1_struct_0(sK7))
    | k1_yellow_0(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1027])).

cnf(c_7501,plain,
    ( k1_yellow_0(sK7,X0) = X1
    | r2_lattice3(sK7,X0,X1) != iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1028])).

cnf(c_1048,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_680])).

cnf(c_1049,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK7,X0,sK5(sK7,X0,X1))
    | ~ r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_yellow_0(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_7500,plain,
    ( k1_yellow_0(sK7,X0) = X1
    | r2_lattice3(sK7,X0,X1) != iProver_top
    | r2_lattice3(sK7,X0,sK5(sK7,X0,X1)) = iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_13258,plain,
    ( k1_yellow_0(sK7,X0) = X1
    | r2_lattice3(sK7,X0,X1) != iProver_top
    | r2_lattice3(sK7,sK8,sK5(sK7,X0,X1)) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK7,X0,X1)) = iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7501,c_10544])).

cnf(c_16989,plain,
    ( k1_yellow_0(sK7,sK8) = X0
    | r2_lattice3(sK7,sK8,X0) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK7,sK8,X0)) = iProver_top
    | r1_yellow_0(sK7,sK8) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7500,c_13258])).

cnf(c_26,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_530,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | sK7 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_531,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7))
    | ~ m1_yellow_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_39,c_36])).

cnf(c_536,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_555,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_536,c_21])).

cnf(c_621,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k1_yellow_0(sK6,sK8) != X0
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(resolution_lifted,[status(thm)],[c_33,c_555])).

cnf(c_622,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0)
    | ~ r1_orders_2(sK6,k1_yellow_0(sK6,sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_747,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0)
    | ~ r1_orders_2(sK6,k1_yellow_0(sK6,sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_665,c_622])).

cnf(c_1216,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0)
    | ~ r1_orders_2(sK6,k1_yellow_0(sK6,sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_800,c_747])).

cnf(c_7491,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0) = iProver_top
    | r1_orders_2(sK6,k1_yellow_0(sK6,sK8),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_8164,plain,
    ( r2_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0) = iProver_top
    | r1_yellow_0(sK6,sK8) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7517,c_7491])).

cnf(c_666,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_11711,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8164,c_49,c_666])).

cnf(c_11712,plain,
    ( r2_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK7,k1_yellow_0(sK6,sK8),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11711])).

cnf(c_1069,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_680])).

cnf(c_1070,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X1,sK5(sK7,X0,X1))
    | ~ r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_yellow_0(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_7499,plain,
    ( k1_yellow_0(sK7,X0) = X1
    | r2_lattice3(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK7,X1,sK5(sK7,X0,X1)) != iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_11718,plain,
    ( k1_yellow_0(sK7,X0) = k1_yellow_0(sK6,sK8)
    | r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK7,X0,k1_yellow_0(sK6,sK8))) != iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(sK5(sK7,X0,k1_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11712,c_7499])).

cnf(c_32099,plain,
    ( m1_subset_1(sK5(sK7,X0,k1_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK7,X0,k1_yellow_0(sK6,sK8))) != iProver_top
    | r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | k1_yellow_0(sK7,X0) = k1_yellow_0(sK6,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11718,c_586])).

cnf(c_32100,plain,
    ( k1_yellow_0(sK7,X0) = k1_yellow_0(sK6,sK8)
    | r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK7,X0,k1_yellow_0(sK6,sK8))) != iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(sK5(sK7,X0,k1_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_32099])).

cnf(c_32105,plain,
    ( k1_yellow_0(sK7,X0) = sK4(sK6,sK8)
    | r2_lattice3(sK7,X0,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK5(sK7,X0,sK4(sK6,sK8))) != iProver_top
    | r1_yellow_0(sK7,X0) != iProver_top
    | m1_subset_1(sK5(sK7,X0,sK4(sK6,sK8)),u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32100,c_12971])).

cnf(c_54767,plain,
    ( k1_yellow_0(sK7,sK8) = sK4(sK6,sK8)
    | r2_lattice3(sK7,sK8,sK4(sK6,sK8)) != iProver_top
    | r1_yellow_0(sK7,sK8) != iProver_top
    | m1_subset_1(sK5(sK7,sK8,sK4(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16989,c_32105])).

cnf(c_12979,plain,
    ( m1_subset_1(sK4(sK6,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12971,c_7523])).

cnf(c_32,negated_conjecture,
    ( ~ r1_yellow_0(sK7,sK8)
    | k1_yellow_0(sK6,sK8) != k1_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_7527,plain,
    ( k1_yellow_0(sK6,sK8) != k1_yellow_0(sK7,sK8)
    | r1_yellow_0(sK7,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_12980,plain,
    ( k1_yellow_0(sK7,sK8) != sK4(sK6,sK8)
    | r1_yellow_0(sK7,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12971,c_7527])).

cnf(c_57227,plain,
    ( m1_subset_1(sK5(sK7,sK8,sK4(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | r1_yellow_0(sK7,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54767,c_12977,c_12979,c_12980])).

cnf(c_57228,plain,
    ( r1_yellow_0(sK7,sK8) != iProver_top
    | m1_subset_1(sK5(sK7,sK8,sK4(sK6,sK8)),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_57227])).

cnf(c_57231,plain,
    ( k1_yellow_0(sK7,sK8) = sK4(sK6,sK8)
    | r2_lattice3(sK7,sK8,sK4(sK6,sK8)) != iProver_top
    | r1_yellow_0(sK7,sK8) != iProver_top
    | m1_subset_1(sK4(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7501,c_57228])).

cnf(c_57519,plain,
    ( r1_yellow_0(sK7,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_57231,c_12977,c_12979,c_12980])).

cnf(c_62669,plain,
    ( sP0(X0,sK7,sK8) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,sK8,X0)) = iProver_top
    | r2_lattice3(sK7,sK8,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17519,c_12977,c_12979,c_12980,c_57231])).

cnf(c_62670,plain,
    ( r2_lattice3(sK7,sK8,X0) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,sK8,X0)) = iProver_top
    | sP0(X0,sK7,sK8) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_62669])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1186,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ sP0(X2,X0,X1)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_680])).

cnf(c_1187,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X1,sK3(sK7,X0,X1))
    | ~ sP0(X1,sK7,X0)
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_7492,plain,
    ( r2_lattice3(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK7,X1,sK3(sK7,X0,X1)) != iProver_top
    | sP0(X1,sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_11719,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,X0,k1_yellow_0(sK6,sK8))) != iProver_top
    | sP0(k1_yellow_0(sK6,sK8),sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top
    | m1_subset_1(sK3(sK7,X0,k1_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11712,c_7492])).

cnf(c_7722,plain,
    ( ~ r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8))
    | ~ sP0(k1_yellow_0(sK6,sK8),sK7,X0)
    | r1_yellow_0(sK7,X0)
    | m1_subset_1(sK3(sK7,X0,k1_yellow_0(sK6,sK8)),u1_struct_0(sK7))
    | ~ m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_7723,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | sP0(k1_yellow_0(sK6,sK8),sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top
    | m1_subset_1(sK3(sK7,X0,k1_yellow_0(sK6,sK8)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(k1_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7722])).

cnf(c_34223,plain,
    ( r2_lattice3(sK7,X0,k1_yellow_0(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,X0,k1_yellow_0(sK6,sK8))) != iProver_top
    | sP0(k1_yellow_0(sK6,sK8),sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11719,c_586,c_7723])).

cnf(c_34229,plain,
    ( r2_lattice3(sK7,X0,sK4(sK6,sK8)) != iProver_top
    | r2_lattice3(sK6,sK8,sK3(sK7,X0,sK4(sK6,sK8))) != iProver_top
    | sP0(sK4(sK6,sK8),sK7,X0) != iProver_top
    | r1_yellow_0(sK7,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34223,c_12971])).

cnf(c_62676,plain,
    ( r2_lattice3(sK7,sK8,sK4(sK6,sK8)) != iProver_top
    | sP0(sK4(sK6,sK8),sK7,sK8) != iProver_top
    | r1_yellow_0(sK7,sK8) = iProver_top
    | m1_subset_1(sK4(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62670,c_34229])).

cnf(c_63170,plain,
    ( sP0(sK4(sK6,sK8),sK7,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62676,c_12977,c_12979,c_12980,c_57231])).

cnf(c_63175,plain,
    ( sK1(sK4(sK6,sK8),sK7,sK8) = sK4(sK6,sK8) ),
    inference(superposition,[status(thm)],[c_41433,c_63170])).

cnf(c_0,plain,
    ( sP0(X0,X1,X2)
    | sK1(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_15009,plain,
    ( sP0(sK4(sK6,sK8),sK7,X0)
    | sK1(sK4(sK6,sK8),sK7,X0) != sK4(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_30465,plain,
    ( sP0(sK4(sK6,sK8),sK7,sK8)
    | sK1(sK4(sK6,sK8),sK7,sK8) != sK4(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_15009])).

cnf(c_30469,plain,
    ( sK1(sK4(sK6,sK8),sK7,sK8) != sK4(sK6,sK8)
    | sP0(sK4(sK6,sK8),sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30465])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63175,c_62676,c_57519,c_30469,c_12979,c_12977])).


%------------------------------------------------------------------------------

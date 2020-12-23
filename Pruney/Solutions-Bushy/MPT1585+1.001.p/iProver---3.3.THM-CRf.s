%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1585+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:57 EST 2020

% Result     : Theorem 27.79s
% Output     : CNFRefutation 27.79s
% Verified   : 
% Statistics : Number of formulae       :  349 (7792 expanded)
%              Number of clauses        :  244 (1907 expanded)
%              Number of leaves         :   26 (2397 expanded)
%              Depth                    :   39
%              Number of atoms          : 1813 (68752 expanded)
%              Number of equality atoms :  623 (7903 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              & r1_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X4,X3)
                | ~ r1_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X4,X3)
                | ~ r1_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X6,X5)
                & r1_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X6,X5)
          & r1_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK3(X1,X2,X5),X5)
        & r1_lattice3(X1,X2,sK3(X1,X2,X5))
        & m1_subset_1(sK3(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X4,X3)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK2(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,X4,sK2(X0,X1,X2))
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r1_lattice3(X1,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK2(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,X4,sK2(X0,X1,X2))
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,sK2(X0,X1,X2))
          & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,sK3(X1,X2,X5),X5)
              & r1_lattice3(X1,X2,sK3(X1,X2,X5))
              & m1_subset_1(sK3(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f54,f56,f55])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,conjecture,(
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
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
               => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                    & r2_yellow_0(X0,X2) )
                 => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                    & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
            | ~ r2_yellow_0(X1,X2) )
          & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
          & r2_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( k2_yellow_0(X0,sK8) != k2_yellow_0(X1,sK8)
          | ~ r2_yellow_0(X1,sK8) )
        & r2_hidden(k2_yellow_0(X0,sK8),u1_struct_0(X1))
        & r2_yellow_0(X0,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_yellow_0(sK7,X2) != k2_yellow_0(X0,X2)
              | ~ r2_yellow_0(sK7,X2) )
            & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(sK7))
            & r2_yellow_0(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
        & m1_yellow_0(sK7,X0)
        & v4_yellow_0(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                  | ~ r2_yellow_0(X1,X2) )
                & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                & r2_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(sK6,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(sK6,X2),u1_struct_0(X1))
              & r2_yellow_0(sK6,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK6)
          & v4_yellow_0(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK6)
      & v4_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( k2_yellow_0(sK6,sK8) != k2_yellow_0(sK7,sK8)
      | ~ r2_yellow_0(sK7,sK8) )
    & r2_hidden(k2_yellow_0(sK6,sK8),u1_struct_0(sK7))
    & r2_yellow_0(sK6,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & m1_yellow_0(sK7,sK6)
    & v4_yellow_0(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_orders_2(sK6)
    & v4_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f45,f65,f64,f63])).

fof(f106,plain,(
    m1_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f103,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f104,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | r1_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,(
    r2_hidden(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f66])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f13,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f105,plain,(
    v4_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,(
    r2_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f66])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,X4,sK2(X0,X1,X2))
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f94])).

fof(f114,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X4,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f8,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,sK2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f107,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X1,X2,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f120,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X0,X2,X4)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( sP0(X2,X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f22,f46])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( sP0(X2,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X2)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( sP0(X4,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f58])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK5(X0,X1),X0,X1)
        & ! [X5] :
            ( r1_orders_2(X0,X5,sK5(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( sP0(sK5(X0,X1),X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X5,sK5(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK5(X0,X1))
              & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
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
    inference(equality_resolution,[],[f95])).

fof(f116,plain,(
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
    inference(equality_resolution,[],[f115])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP0(sK5(X0,X1),X0,X1)
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f73,plain,(
    ! [X2,X0,X5,X1] :
      ( X0 = X5
      | r1_lattice3(X1,X2,sK3(X1,X2,X5))
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f72,plain,(
    ! [X2,X0,X5,X1] :
      ( X0 = X5
      | m1_subset_1(sK3(X1,X2,X5),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f110,plain,
    ( k2_yellow_0(sK6,sK8) != k2_yellow_0(sK7,sK8)
    | ~ r2_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f66])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK2(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7640,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_26,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_38,negated_conjecture,
    ( m1_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | sK7 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_724,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_41,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_728,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_43,c_41,c_40])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_7631,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_8133,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | m1_subset_1(sK2(X0,sK7,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7640,c_7631])).

cnf(c_1,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_947,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | k2_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_41])).

cnf(c_948,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r1_lattice3(sK6,X0,sK1(sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0)
    | k2_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_7618,plain,
    ( k2_yellow_0(sK6,X0) = X1
    | r1_lattice3(sK6,X0,X1) != iProver_top
    | r1_lattice3(sK6,X0,sK1(sK6,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_2,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_926,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | k2_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_41])).

cnf(c_927,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0)
    | k2_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_7619,plain,
    ( k2_yellow_0(sK6,X0) = X1
    | r1_lattice3(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_3,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_19,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_19])).

cnf(c_274,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_273])).

cnf(c_833,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_274,c_41])).

cnf(c_834,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_7626,plain,
    ( r1_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_648,plain,
    ( m1_subset_1(X0,X1)
    | k2_yellow_0(sK6,sK8) != X0
    | u1_struct_0(sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_649,plain,
    ( m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_7632,plain,
    ( m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_266,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_19])).

cnf(c_851,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_41])).

cnf(c_852,plain,
    ( r1_lattice3(sK6,X0,k2_yellow_0(sK6,X0))
    | ~ r2_yellow_0(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_851])).

cnf(c_7625,plain,
    ( r1_lattice3(sK6,X0,k2_yellow_0(sK6,X0)) = iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_30,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_39,negated_conjecture,
    ( v4_yellow_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_570,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X1,X2)
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | sK7 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_39])).

cnf(c_571,plain,
    ( r1_lattice3(sK7,X0,X1)
    | ~ r1_lattice3(sK6,X0,X1)
    | ~ m1_yellow_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_lattice3(sK7,X0,X1)
    | ~ r1_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_43,c_41,c_40,c_38])).

cnf(c_576,plain,
    ( r1_lattice3(sK7,X0,X1)
    | ~ r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_575])).

cnf(c_810,plain,
    ( r1_lattice3(sK7,X0,X1)
    | ~ r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_729,c_576])).

cnf(c_7628,plain,
    ( r1_lattice3(sK7,X0,X1) = iProver_top
    | r1_lattice3(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_9311,plain,
    ( r1_lattice3(sK7,X0,k2_yellow_0(sK6,X0)) = iProver_top
    | m1_subset_1(k2_yellow_0(sK6,X0),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7625,c_7628])).

cnf(c_9450,plain,
    ( r1_lattice3(sK7,sK8,k2_yellow_0(sK6,sK8)) = iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7632,c_9311])).

cnf(c_650,plain,
    ( m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_36,negated_conjecture,
    ( r2_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2974,plain,
    ( r1_lattice3(sK6,X0,k2_yellow_0(sK6,X0))
    | sK8 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_852])).

cnf(c_2975,plain,
    ( r1_lattice3(sK6,sK8,k2_yellow_0(sK6,sK8)) ),
    inference(unflattening,[status(thm)],[c_2974])).

cnf(c_2976,plain,
    ( r1_lattice3(sK6,sK8,k2_yellow_0(sK6,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2975])).

cnf(c_7842,plain,
    ( r1_lattice3(sK7,X0,k2_yellow_0(sK6,sK8))
    | ~ r1_lattice3(sK6,X0,k2_yellow_0(sK6,sK8))
    | ~ m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_8030,plain,
    ( r1_lattice3(sK7,sK8,k2_yellow_0(sK6,sK8))
    | ~ r1_lattice3(sK6,sK8,k2_yellow_0(sK6,sK8))
    | ~ m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7842])).

cnf(c_8031,plain,
    ( r1_lattice3(sK7,sK8,k2_yellow_0(sK6,sK8)) = iProver_top
    | r1_lattice3(sK6,sK8,k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8030])).

cnf(c_9453,plain,
    ( r1_lattice3(sK7,sK8,k2_yellow_0(sK6,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9450,c_650,c_2976,c_8031])).

cnf(c_6,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_orders_2(X1,X3,sK2(X0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7642,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_lattice3(X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,sK2(X0,X1,X2)) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_27,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_780,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | sK7 != X0
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_781,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_41,c_729])).

cnf(c_786,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_796,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_786,c_729])).

cnf(c_7629,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_9572,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | r1_orders_2(sK7,X2,sK2(X0,sK7,X1)) != iProver_top
    | r1_orders_2(sK6,X2,sK2(X0,sK7,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7640,c_7629])).

cnf(c_9803,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | r1_lattice3(sK7,X1,X2) != iProver_top
    | r1_orders_2(sK6,X2,sK2(X0,sK7,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7642,c_9572])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_537,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_42])).

cnf(c_538,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X1,X2)
    | r1_orders_2(sK6,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_orders_2(sK6,X0,X2)
    | ~ r1_orders_2(sK6,X1,X2)
    | ~ r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_41])).

cnf(c_541,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X2,X0)
    | r1_orders_2(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_7633,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X0) != iProver_top
    | r1_orders_2(sK6,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_9878,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | r1_lattice3(sK7,X1,X2) != iProver_top
    | r1_orders_2(sK6,X3,X2) != iProver_top
    | r1_orders_2(sK6,X3,sK2(X0,sK7,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(X0,sK7,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9803,c_7633])).

cnf(c_15818,plain,
    ( m1_subset_1(X3,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK6,X3,sK2(X0,sK7,X1)) = iProver_top
    | r1_orders_2(sK6,X3,X2) != iProver_top
    | r1_lattice3(sK7,X1,X2) != iProver_top
    | sP0(X0,sK7,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9878,c_8133])).

cnf(c_15819,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | r1_lattice3(sK7,X1,X2) != iProver_top
    | r1_orders_2(sK6,X3,X2) != iProver_top
    | r1_orders_2(sK6,X3,sK2(X0,sK7,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15818])).

cnf(c_15828,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,X1,sK2(X0,sK7,sK8)) = iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9453,c_15819])).

cnf(c_7730,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7))
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_7731,plain,
    ( m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7730])).

cnf(c_41812,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,X1,sK2(X0,sK7,sK8)) = iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15828,c_650,c_7731])).

cnf(c_0,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_968,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | k2_yellow_0(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_41])).

cnf(c_969,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | ~ r1_orders_2(sK6,sK1(sK6,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0)
    | k2_yellow_0(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_968])).

cnf(c_7617,plain,
    ( k2_yellow_0(sK6,X0) = X1
    | r1_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,sK1(sK6,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_969])).

cnf(c_41831,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,X1)
    | sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | r1_orders_2(sK6,sK1(sK6,X1,sK2(X0,sK7,sK8)),k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,X1,sK2(X0,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_41812,c_7617])).

cnf(c_42788,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,X1)
    | sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | r1_lattice3(sK6,sK8,sK1(sK6,X1,sK2(X0,sK7,sK8))) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,X1,sK2(X0,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X1) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7626,c_41831])).

cnf(c_51,plain,
    ( r2_yellow_0(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42973,plain,
    ( r2_yellow_0(sK6,X1) != iProver_top
    | m1_subset_1(sK1(sK6,X1,sK2(X0,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r1_lattice3(sK6,sK8,sK1(sK6,X1,sK2(X0,sK7,sK8))) != iProver_top
    | r1_lattice3(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | sP0(X0,sK7,sK8) = iProver_top
    | sK2(X0,sK7,sK8) = k2_yellow_0(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42788,c_51])).

cnf(c_42974,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,X1)
    | sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | r1_lattice3(sK6,sK8,sK1(sK6,X1,sK2(X0,sK7,sK8))) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,X1,sK2(X0,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_42973])).

cnf(c_42979,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,X1)
    | sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | r1_lattice3(sK6,sK8,sK1(sK6,X1,sK2(X0,sK7,sK8))) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7619,c_42974])).

cnf(c_42984,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,sK8)
    | sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK6,sK8,sK2(X0,sK7,sK8)) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7618,c_42979])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2)
    | r1_lattice3(X1,X2,sK2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7641,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_lattice3(X1,X2,sK2(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_7634,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X1,X2)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_752,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X3)
    | sK7 != X0
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_753,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_lattice3(sK6,X0,X1)
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_43,c_41,c_40])).

cnf(c_758,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_757])).

cnf(c_768,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_758,c_729])).

cnf(c_7630,plain,
    ( r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_10150,plain,
    ( r1_lattice3(sK7,sK8,X0) != iProver_top
    | r1_lattice3(sK6,sK8,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7634,c_7630])).

cnf(c_10155,plain,
    ( sP0(X0,sK7,X1) = iProver_top
    | r1_lattice3(sK7,sK8,sK2(X0,sK7,X1)) != iProver_top
    | r1_lattice3(sK6,sK8,sK2(X0,sK7,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7640,c_10150])).

cnf(c_10802,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK6,sK8,sK2(X0,sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7641,c_10155])).

cnf(c_43181,plain,
    ( m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | sK2(X0,sK7,sK8) = k2_yellow_0(sK6,sK8)
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42984,c_51,c_10802])).

cnf(c_43182,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,sK8)
    | sP0(X0,sK7,sK8) = iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_43181])).

cnf(c_43187,plain,
    ( sK2(X0,sK7,sK8) = k2_yellow_0(sK6,sK8)
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_8133,c_43182])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | r1_lattice3(X1,X2,sK4(X1,X2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_21,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_741,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_742,plain,
    ( l1_orders_2(sK7)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_744,plain,
    ( l1_orders_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_41])).

cnf(c_1229,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | r1_lattice3(X1,X2,sK4(X1,X2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_744])).

cnf(c_1230,plain,
    ( ~ sP0(X0,sK7,X1)
    | ~ r1_lattice3(sK7,X1,X0)
    | r1_lattice3(sK7,X1,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_1229])).

cnf(c_7602,plain,
    ( sP0(X0,sK7,X1) != iProver_top
    | r1_lattice3(sK7,X1,X0) != iProver_top
    | r1_lattice3(sK7,X1,sK4(sK7,X1,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_25,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_594,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | sK7 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_595,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7))
    | ~ m1_yellow_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_41,c_38])).

cnf(c_600,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_599])).

cnf(c_619,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_600,c_23])).

cnf(c_655,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_xboole_0(X3)
    | X0 != X2
    | u1_struct_0(sK7) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_619])).

cnf(c_656,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_641,plain,
    ( ~ v1_xboole_0(X0)
    | k2_yellow_0(sK6,sK8) != X1
    | u1_struct_0(sK7) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_642,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_642])).

cnf(c_661,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_660])).

cnf(c_812,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_729,c_661])).

cnf(c_7627,plain,
    ( r1_orders_2(sK7,X0,X1) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_730,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_813,plain,
    ( r1_orders_2(sK7,X0,X1) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_10565,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK7,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7627,c_730,c_813])).

cnf(c_10566,plain,
    ( r1_orders_2(sK7,X0,X1) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10565])).

cnf(c_10570,plain,
    ( r1_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK7,X1,k2_yellow_0(sK6,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,X0),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7626,c_10566])).

cnf(c_11171,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK7,X0,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7632,c_10570])).

cnf(c_11657,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK7,X0,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11171,c_51,c_730])).

cnf(c_9573,plain,
    ( r1_orders_2(sK7,X0,k2_yellow_0(sK6,sK8)) != iProver_top
    | r1_orders_2(sK6,X0,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7632,c_7629])).

cnf(c_11666,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X0,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11657,c_9573])).

cnf(c_17699,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X1,X0) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11666,c_7633])).

cnf(c_17726,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X1,X0) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17699,c_650,c_730,c_7731])).

cnf(c_17739,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10802,c_17726])).

cnf(c_21105,plain,
    ( sP0(X0,sK7,sK8)
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_21106,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | m1_subset_1(sK2(X0,sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21105])).

cnf(c_22432,plain,
    ( m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | r1_orders_2(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17739,c_21106])).

cnf(c_22433,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,X1,sK2(X0,sK7,sK8)) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22432])).

cnf(c_22438,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK7,sK8,X1) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9803,c_22433])).

cnf(c_22444,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK7,sK8,X1) != iProver_top
    | r1_orders_2(sK7,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22438,c_10566])).

cnf(c_41246,plain,
    ( m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | r1_lattice3(sK7,sK8,X1) != iProver_top
    | sP0(X0,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22444,c_650])).

cnf(c_41247,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | r1_lattice3(sK7,sK8,X1) != iProver_top
    | r1_orders_2(sK7,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_41246])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | ~ r1_orders_2(X1,sK4(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1250,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | ~ r1_orders_2(X1,sK4(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_744])).

cnf(c_1251,plain,
    ( ~ sP0(X0,sK7,X1)
    | ~ r1_lattice3(sK7,X1,X0)
    | ~ r1_orders_2(sK7,sK4(sK7,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_1250])).

cnf(c_7601,plain,
    ( sP0(X0,sK7,X1) != iProver_top
    | r1_lattice3(sK7,X1,X0) != iProver_top
    | r1_orders_2(sK7,sK4(sK7,X1,X0),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_41254,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | sP0(k2_yellow_0(sK6,sK8),sK7,X1) != iProver_top
    | r1_lattice3(sK7,X1,k2_yellow_0(sK6,sK8)) != iProver_top
    | r1_lattice3(sK7,sK8,sK4(sK7,X1,k2_yellow_0(sK6,sK8))) != iProver_top
    | m1_subset_1(sK4(sK7,X1,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X1,k2_yellow_0(sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_41247,c_7601])).

cnf(c_99758,plain,
    ( m1_subset_1(sK4(sK7,X1,k2_yellow_0(sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK7,X1,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | r1_lattice3(sK7,sK8,sK4(sK7,X1,k2_yellow_0(sK6,sK8))) != iProver_top
    | r1_lattice3(sK7,X1,k2_yellow_0(sK6,sK8)) != iProver_top
    | sP0(k2_yellow_0(sK6,sK8),sK7,X1) != iProver_top
    | sP0(X0,sK7,sK8) = iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41254,c_650])).

cnf(c_99759,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | sP0(k2_yellow_0(sK6,sK8),sK7,X1) != iProver_top
    | r1_lattice3(sK7,X1,k2_yellow_0(sK6,sK8)) != iProver_top
    | r1_lattice3(sK7,sK8,sK4(sK7,X1,k2_yellow_0(sK6,sK8))) != iProver_top
    | m1_subset_1(sK4(sK7,X1,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X1,k2_yellow_0(sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_99758])).

cnf(c_99764,plain,
    ( sP0(X0,sK7,sK8) = iProver_top
    | sP0(k2_yellow_0(sK6,sK8),sK7,sK8) != iProver_top
    | r1_lattice3(sK7,sK8,k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(sK4(sK7,sK8,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,sK8,k2_yellow_0(sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7602,c_99759])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1208,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_744])).

cnf(c_1209,plain,
    ( ~ sP0(X0,sK7,X1)
    | ~ r1_lattice3(sK7,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | r2_yellow_0(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_1208])).

cnf(c_7603,plain,
    ( sP0(X0,sK7,X1) != iProver_top
    | r1_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7)) = iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_10159,plain,
    ( sP0(X0,sK7,X1) != iProver_top
    | r1_lattice3(sK7,X1,X0) != iProver_top
    | r1_lattice3(sK7,sK8,sK4(sK7,X1,X0)) != iProver_top
    | r1_lattice3(sK6,sK8,sK4(sK7,X1,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7603,c_10150])).

cnf(c_15230,plain,
    ( sP0(X0,sK7,sK8) != iProver_top
    | r1_lattice3(sK7,sK8,X0) != iProver_top
    | r1_lattice3(sK6,sK8,sK4(sK7,sK8,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7602,c_10159])).

cnf(c_11665,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,X0) != iProver_top
    | r1_lattice3(sK7,X0,k2_yellow_0(sK6,sK8)) != iProver_top
    | r1_lattice3(sK6,sK8,sK4(sK7,X0,k2_yellow_0(sK6,sK8))) != iProver_top
    | m1_subset_1(sK4(sK7,X0,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11657,c_7601])).

cnf(c_7831,plain,
    ( ~ sP0(k2_yellow_0(sK6,sK8),sK7,X0)
    | ~ r1_lattice3(sK7,X0,k2_yellow_0(sK6,sK8))
    | m1_subset_1(sK4(sK7,X0,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_7832,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,X0) != iProver_top
    | r1_lattice3(sK7,X0,k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(sK4(sK7,X0,k2_yellow_0(sK6,sK8)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7831])).

cnf(c_27172,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,X0) != iProver_top
    | r1_lattice3(sK7,X0,k2_yellow_0(sK6,sK8)) != iProver_top
    | r1_lattice3(sK6,sK8,sK4(sK7,X0,k2_yellow_0(sK6,sK8))) != iProver_top
    | r2_yellow_0(sK7,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11665,c_650,c_7832])).

cnf(c_40329,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,sK8) != iProver_top
    | r1_lattice3(sK7,sK8,k2_yellow_0(sK6,sK8)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_15230,c_27172])).

cnf(c_15,plain,
    ( sP0(sK5(X0,X1),X0,X1)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1070,plain,
    ( sP0(sK5(X0,X1),X0,X1)
    | ~ r2_yellow_0(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_744])).

cnf(c_1071,plain,
    ( sP0(sK5(sK7,X0),sK7,X0)
    | ~ r2_yellow_0(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_1070])).

cnf(c_7610,plain,
    ( sP0(sK5(sK7,X0),sK7,X0) = iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X2,sK3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X3 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7638,plain,
    ( X0 = X1
    | sP0(X1,X2,X3) != iProver_top
    | r1_lattice3(X2,X3,X0) != iProver_top
    | r1_lattice3(X2,X3,sK3(X2,X3,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8917,plain,
    ( sK5(sK7,X0) = X1
    | r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_lattice3(sK7,X0,sK3(sK7,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7610,c_7638])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))
    | X3 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7637,plain,
    ( X0 = X1
    | sP0(X1,X2,X3) != iProver_top
    | r1_lattice3(X2,X3,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK3(X2,X3,X0),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8918,plain,
    ( sK5(sK7,X0) = X1
    | r1_lattice3(sK7,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7610,c_7637])).

cnf(c_10160,plain,
    ( sK5(sK7,X0) = X1
    | r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_lattice3(sK7,sK8,sK3(sK7,X0,X1)) != iProver_top
    | r1_lattice3(sK6,sK8,sK3(sK7,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8918,c_10150])).

cnf(c_14726,plain,
    ( sK5(sK7,sK8) = X0
    | r1_lattice3(sK7,sK8,X0) != iProver_top
    | r1_lattice3(sK6,sK8,sK3(sK7,sK8,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8917,c_10160])).

cnf(c_21168,plain,
    ( sK5(sK7,sK8) = X0
    | r1_lattice3(sK7,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X1,sK3(sK7,sK8,X0)) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK6,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK3(sK7,sK8,X0),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_14726,c_17726])).

cnf(c_34,negated_conjecture,
    ( ~ r2_yellow_0(sK7,sK8)
    | k2_yellow_0(sK6,sK8) != k2_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_53,plain,
    ( k2_yellow_0(sK6,sK8) != k2_yellow_0(sK7,sK8)
    | r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6873,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6898,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_6873])).

cnf(c_9435,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_6873])).

cnf(c_1007,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_744])).

cnf(c_1008,plain,
    ( r1_lattice3(sK7,X0,k2_yellow_0(sK7,X0))
    | ~ r2_yellow_0(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_1007])).

cnf(c_7615,plain,
    ( r1_lattice3(sK7,X0,k2_yellow_0(sK7,X0)) = iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_1019,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_744])).

cnf(c_1020,plain,
    ( m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_7614,plain,
    ( m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_10157,plain,
    ( r1_lattice3(sK7,sK8,k2_yellow_0(sK7,X0)) != iProver_top
    | r1_lattice3(sK6,sK8,k2_yellow_0(sK7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7614,c_10150])).

cnf(c_10250,plain,
    ( r1_lattice3(sK6,sK8,k2_yellow_0(sK7,sK8)) = iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7615,c_10157])).

cnf(c_6875,plain,
    ( X0 != X1
    | X2 != X3
    | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X3) ),
    theory(equality)).

cnf(c_9763,plain,
    ( X0 != sK8
    | X1 != sK6
    | k2_yellow_0(X1,X0) = k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_6875])).

cnf(c_16061,plain,
    ( X0 != sK6
    | k2_yellow_0(X0,sK8) = k2_yellow_0(sK6,sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_9763])).

cnf(c_16062,plain,
    ( k2_yellow_0(sK6,sK8) = k2_yellow_0(sK6,sK8)
    | sK8 != sK8
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_16061])).

cnf(c_863,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_864,plain,
    ( m1_subset_1(k2_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_7624,plain,
    ( m1_subset_1(k2_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_989,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_274,c_744])).

cnf(c_990,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_orders_2(sK7,X1,k2_yellow_0(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_989])).

cnf(c_7616,plain,
    ( r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK7,X1,k2_yellow_0(sK7,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_9574,plain,
    ( r1_orders_2(sK7,X0,k2_yellow_0(sK7,X1)) != iProver_top
    | r1_orders_2(sK6,X0,k2_yellow_0(sK7,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7614,c_7629])).

cnf(c_17061,plain,
    ( r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK6,X1,k2_yellow_0(sK7,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7616,c_9574])).

cnf(c_18584,plain,
    ( r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X1) != iProver_top
    | r1_orders_2(sK6,X2,k2_yellow_0(sK7,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17061,c_7633])).

cnf(c_1021,plain,
    ( m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_7806,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK7))
    | m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_7807,plain,
    ( m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7806])).

cnf(c_18609,plain,
    ( m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK6,X2,k2_yellow_0(sK7,X0)) = iProver_top
    | r1_orders_2(sK6,X2,X1) != iProver_top
    | r1_lattice3(sK7,X0,X1) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18584,c_1021,c_7807])).

cnf(c_18610,plain,
    ( r1_lattice3(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X1) != iProver_top
    | r1_orders_2(sK6,X2,k2_yellow_0(sK7,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18609])).

cnf(c_18614,plain,
    ( r1_lattice3(sK7,X0,k2_yellow_0(sK6,X1)) != iProver_top
    | r1_lattice3(sK6,X1,X2) != iProver_top
    | r1_orders_2(sK6,X2,k2_yellow_0(sK7,X0)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,X1),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,X1),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top
    | r2_yellow_0(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7626,c_18610])).

cnf(c_19052,plain,
    ( r1_lattice3(sK7,X0,k2_yellow_0(sK6,X1)) != iProver_top
    | r1_lattice3(sK6,X1,X2) != iProver_top
    | r1_orders_2(sK6,X2,k2_yellow_0(sK7,X0)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,X1),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0) != iProver_top
    | r2_yellow_0(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7624,c_18614])).

cnf(c_19057,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X0,k2_yellow_0(sK7,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK6,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9453,c_19052])).

cnf(c_21003,plain,
    ( r2_yellow_0(sK7,sK8) != iProver_top
    | r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X0,k2_yellow_0(sK7,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19057,c_51,c_650])).

cnf(c_21004,plain,
    ( r1_lattice3(sK6,sK8,X0) != iProver_top
    | r1_orders_2(sK6,X0,k2_yellow_0(sK7,sK8)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_21003])).

cnf(c_21017,plain,
    ( k2_yellow_0(sK6,X0) = k2_yellow_0(sK7,sK8)
    | r1_lattice3(sK6,X0,k2_yellow_0(sK7,sK8)) != iProver_top
    | r1_lattice3(sK6,sK8,sK1(sK6,X0,k2_yellow_0(sK7,sK8))) != iProver_top
    | m1_subset_1(sK1(sK6,X0,k2_yellow_0(sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top
    | r2_yellow_0(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21004,c_7617])).

cnf(c_21492,plain,
    ( k2_yellow_0(sK7,sK8) = k2_yellow_0(sK6,sK8)
    | r1_lattice3(sK6,sK8,k2_yellow_0(sK7,sK8)) != iProver_top
    | m1_subset_1(sK1(sK6,sK8,k2_yellow_0(sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7618,c_21017])).

cnf(c_21881,plain,
    ( r2_yellow_0(sK7,sK8) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,sK8,k2_yellow_0(sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | k2_yellow_0(sK7,sK8) = k2_yellow_0(sK6,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21492,c_51,c_10250])).

cnf(c_21882,plain,
    ( k2_yellow_0(sK7,sK8) = k2_yellow_0(sK6,sK8)
    | m1_subset_1(sK1(sK6,sK8,k2_yellow_0(sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_21881])).

cnf(c_21885,plain,
    ( k2_yellow_0(sK7,sK8) = k2_yellow_0(sK6,sK8)
    | r1_lattice3(sK6,sK8,k2_yellow_0(sK7,sK8)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_yellow_0(sK7,sK8) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7619,c_21882])).

cnf(c_38216,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_7806])).

cnf(c_38217,plain,
    ( m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38216])).

cnf(c_49696,plain,
    ( m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_49697,plain,
    ( m1_subset_1(k2_yellow_0(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49696])).

cnf(c_6874,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9697,plain,
    ( X0 != X1
    | X0 = k2_yellow_0(sK7,X2)
    | k2_yellow_0(sK7,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_6874])).

cnf(c_16276,plain,
    ( X0 != k2_yellow_0(X1,X2)
    | X0 = k2_yellow_0(sK7,X3)
    | k2_yellow_0(sK7,X3) != k2_yellow_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_9697])).

cnf(c_20389,plain,
    ( k2_yellow_0(sK7,X0) != k2_yellow_0(sK6,sK8)
    | k2_yellow_0(sK6,sK8) = k2_yellow_0(sK7,X0)
    | k2_yellow_0(sK6,sK8) != k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_16276])).

cnf(c_67274,plain,
    ( k2_yellow_0(sK7,sK8) != k2_yellow_0(sK6,sK8)
    | k2_yellow_0(sK6,sK8) = k2_yellow_0(sK7,sK8)
    | k2_yellow_0(sK6,sK8) != k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_20389])).

cnf(c_75560,plain,
    ( r2_yellow_0(sK7,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21168,c_51,c_53,c_6898,c_9435,c_10250,c_16062,c_21885,c_38217,c_49697,c_67274])).

cnf(c_99769,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_99764,c_51,c_53,c_650,c_2976,c_6898,c_8031,c_9435,c_10250,c_16062,c_21885,c_38217,c_40329,c_49697,c_67274])).

cnf(c_99793,plain,
    ( sK2(k2_yellow_0(sK6,sK8),sK7,sK8) = k2_yellow_0(sK6,sK8) ),
    inference(superposition,[status(thm)],[c_43187,c_99769])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2)
    | sK2(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8077,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,X0)
    | sK2(k2_yellow_0(sK6,sK8),sK7,X0) != k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9224,plain,
    ( sP0(k2_yellow_0(sK6,sK8),sK7,sK8)
    | sK2(k2_yellow_0(sK6,sK8),sK7,sK8) != k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_8077])).

cnf(c_9225,plain,
    ( sK2(k2_yellow_0(sK6,sK8),sK7,sK8) != k2_yellow_0(sK6,sK8)
    | sP0(k2_yellow_0(sK6,sK8),sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9224])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99793,c_75560,c_40329,c_9225,c_8031,c_2976,c_650])).


%------------------------------------------------------------------------------

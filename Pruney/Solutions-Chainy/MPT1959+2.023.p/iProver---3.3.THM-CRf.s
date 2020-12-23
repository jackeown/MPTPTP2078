%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:28 EST 2020

% Result     : Theorem 23.77s
% Output     : CNFRefutation 23.77s
% Verified   : 
% Statistics : Number of formulae       :  243 (1213 expanded)
%              Number of clauses        :  140 ( 372 expanded)
%              Number of leaves         :   34 ( 246 expanded)
%              Depth                    :   31
%              Number of atoms          : 1008 (8427 expanded)
%              Number of equality atoms :  311 ( 759 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
          | ~ r2_hidden(sK1(X0,X1,X2),X1) )
        & ( r2_hidden(sK1(X0,X1,X2),X2)
          | r2_hidden(sK1(X0,X1,X2),X1) )
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
              | ~ r2_hidden(sK1(X0,X1,X2),X1) )
            & ( r2_hidden(sK1(X0,X1,X2),X2)
              | r2_hidden(sK1(X0,X1,X2),X1) )
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f63,f64])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f120,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f23,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK8)
          | ~ v1_subset_1(sK8,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK8)
          | v1_subset_1(sK8,u1_struct_0(X0)) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK8,X0)
        & ~ v1_xboole_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK7),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK7)) )
          & ( ~ r2_hidden(k3_yellow_0(sK7),X1)
            | v1_subset_1(X1,u1_struct_0(sK7)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
          & v13_waybel_0(X1,sK7)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK7)
      & v1_yellow_0(sK7)
      & v5_orders_2(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ( r2_hidden(k3_yellow_0(sK7),sK8)
      | ~ v1_subset_1(sK8,u1_struct_0(sK7)) )
    & ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
      | v1_subset_1(sK8,u1_struct_0(sK7)) )
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & v13_waybel_0(sK8,sK7)
    & ~ v1_xboole_0(sK8)
    & l1_orders_2(sK7)
    & v1_yellow_0(sK7)
    & v5_orders_2(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f73,f75,f74])).

fof(f117,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f76])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f66])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r1_orders_2(X0,X2,sK6(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK5(X0,X1),X3)
            & r2_hidden(sK5(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK6(X0,X1),X1)
                & r1_orders_2(X0,sK5(X0,X1),sK6(X0,X1))
                & r2_hidden(sK5(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f67,f69,f68])).

fof(f103,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f114,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f116,plain,(
    v13_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f94,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f112,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f113,plain,(
    v1_yellow_0(sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f119,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | ~ v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f76])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f102,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f115,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f76])).

fof(f118,plain,
    ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f76])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2(X0),X0)
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f55])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1516,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK1(X2,X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1521,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1519,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1511,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3619,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1511])).

cnf(c_5378,plain,
    ( m1_subset_1(sK0(k1_xboole_0,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_3619])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2907,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_3321,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),X1)
    | r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2907,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3643,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3321,c_0])).

cnf(c_3644,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3643])).

cnf(c_10923,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5378,c_3644])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1508,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1510,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5226,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X1,sK3(X0,X1,X2)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1510])).

cnf(c_10929,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10923,c_5226])).

cnf(c_76074,plain,
    ( X0 = X1
    | r2_lattice3(X2,k1_xboole_0,sK1(u1_struct_0(X2),X0,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_10929])).

cnf(c_21,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_23,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_23])).

cnf(c_461,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_1480,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2) = iProver_top
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1488,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1493,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | v13_waybel_0(X3,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1781,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | v13_waybel_0(X3,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1493,c_1511])).

cnf(c_8847,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | v13_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1781])).

cnf(c_39,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_46,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( v13_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_48,plain,
    ( v13_waybel_0(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9358,plain,
    ( r2_hidden(X1,sK8) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8847,c_46,c_48])).

cnf(c_9359,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_9358])).

cnf(c_9372,plain,
    ( X0 = X1
    | r1_orders_2(sK7,X2,sK1(u1_struct_0(sK7),X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(X2,sK8) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_9359])).

cnf(c_11264,plain,
    ( X0 = X1
    | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X1,X0)) != iProver_top
    | r1_yellow_0(sK7,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK7),X1,X0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
    | r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_9372])).

cnf(c_18312,plain,
    ( r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK7),X1,X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r1_yellow_0(sK7,X2) != iProver_top
    | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X1,X0)) != iProver_top
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11264,c_46])).

cnf(c_18313,plain,
    ( X0 = X1
    | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X1,X0)) != iProver_top
    | r1_yellow_0(sK7,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK7),X1,X0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
    | r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_18312])).

cnf(c_18324,plain,
    ( X0 = X1
    | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X0,X1)) != iProver_top
    | r1_yellow_0(sK7,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top
    | r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18313,c_1516])).

cnf(c_87845,plain,
    ( X0 = X1
    | r1_yellow_0(sK7,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
    | r2_hidden(k1_yellow_0(sK7,k1_xboole_0),sK8) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_76074,c_18324])).

cnf(c_1485,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_17,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1505,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2260,plain,
    ( k1_yellow_0(sK7,k1_xboole_0) = k3_yellow_0(sK7) ),
    inference(superposition,[status(thm)],[c_1485,c_1505])).

cnf(c_87925,plain,
    ( X0 = X1
    | r1_yellow_0(sK7,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top
    | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_87845,c_2260])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_43,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_44,plain,
    ( v5_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_yellow_0(sK7) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_45,plain,
    ( v1_yellow_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_34,negated_conjecture,
    ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_51,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_74,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_76,plain,
    ( r1_yellow_0(sK7,k1_xboole_0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v5_orders_2(sK7) != iProver_top
    | v1_yellow_0(sK7) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_32,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_506,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3049,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_32,c_506])).

cnf(c_7202,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l1_orders_2(u1_struct_0(sK7))
    | l1_orders_2(sK8) ),
    inference(resolution,[status(thm)],[c_3049,c_36])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_35,negated_conjecture,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_24,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_78,plain,
    ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_507,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_523,plain,
    ( k3_yellow_0(sK7) = k3_yellow_0(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_496,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_531,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_2357,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | X0 = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2768,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | sK8 = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2047,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(X2),u1_struct_0(X2))
    | X0 != k3_yellow_0(X2)
    | X1 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_3198,plain,
    ( m1_subset_1(X0,sK8)
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | X0 != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_3671,plain,
    ( m1_subset_1(k3_yellow_0(X0),sK8)
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | k3_yellow_0(X0) != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3198])).

cnf(c_3674,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | m1_subset_1(k3_yellow_0(sK7),sK8)
    | k3_yellow_0(sK7) != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3671])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6027,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK7),sK8)
    | r2_hidden(k3_yellow_0(sK7),sK8)
    | v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7342,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7202,c_39,c_38,c_36,c_35,c_78,c_523,c_531,c_2768,c_3674,c_6027])).

cnf(c_7344,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7342])).

cnf(c_88709,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87925,c_43,c_44,c_45,c_46,c_51,c_76,c_7344])).

cnf(c_88710,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_88709])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3962,plain,
    ( r2_hidden(X0,u1_struct_0(sK7)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1520])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0,X2),X2)
    | ~ r2_hidden(sK1(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1518,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK1(X2,X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X2,X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_88720,plain,
    ( sK8 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_88710,c_1518])).

cnf(c_49,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_89294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | sK8 = X0
    | r2_hidden(sK1(u1_struct_0(sK7),X0,sK8),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_88720,c_49])).

cnf(c_89295,plain,
    ( sK8 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X0,sK8),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_89294])).

cnf(c_89307,plain,
    ( u1_struct_0(sK7) = sK8
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),u1_struct_0(sK7),sK8),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_89295])).

cnf(c_505,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_521,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_8,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1990,plain,
    ( m1_subset_1(sK2(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1996,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_1995,plain,
    ( m1_subset_1(sK2(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1990])).

cnf(c_1997,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2180,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_2776,plain,
    ( v1_subset_1(sK2(u1_struct_0(X0)),u1_struct_0(X0))
    | ~ m1_subset_1(sK2(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | sK2(u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_2778,plain,
    ( v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
    | sK2(u1_struct_0(sK7)) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_499,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2542,plain,
    ( X0 != u1_struct_0(sK7)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_3454,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_3456,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | k1_zfmisc_1(u1_struct_0(sK7)) = k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_497,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2162,plain,
    ( X0 != X1
    | X0 = sK8
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_3207,plain,
    ( X0 != u1_struct_0(sK7)
    | X0 = sK8
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_4613,plain,
    ( sK2(u1_struct_0(sK7)) != u1_struct_0(sK7)
    | sK2(u1_struct_0(sK7)) = sK8
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3207])).

cnf(c_7,plain,
    ( ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7235,plain,
    ( ~ v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2560,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_4179,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_7633,plain,
    ( u1_struct_0(sK7) != sK8
    | sK8 = u1_struct_0(sK7)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_4179])).

cnf(c_501,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3458,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | X1 != u1_struct_0(sK7)
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_6777,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | X0 != sK8
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_15680,plain,
    ( v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(X0))
    | ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK2(u1_struct_0(sK7)) != sK8 ),
    inference(instantiation,[status(thm)],[c_6777])).

cnf(c_15682,plain,
    ( v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | sK2(u1_struct_0(sK7)) != sK8 ),
    inference(instantiation,[status(thm)],[c_15680])).

cnf(c_2321,plain,
    ( X0 != X1
    | X0 = sK2(X2)
    | sK2(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_4354,plain,
    ( u1_struct_0(X0) != X1
    | u1_struct_0(X0) = sK2(X2)
    | sK2(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_9645,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = sK2(X2)
    | sK2(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_4354])).

cnf(c_22643,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = sK2(u1_struct_0(X1))
    | sK2(u1_struct_0(X1)) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_9645])).

cnf(c_22644,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK7) = sK2(u1_struct_0(sK7))
    | sK2(u1_struct_0(sK7)) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_22643])).

cnf(c_2037,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
    | X0 != sK2(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_4337,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
    | X0 != sK2(X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_11020,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
    | X0 != sK2(X2)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_4337])).

cnf(c_24047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK2(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != sK2(u1_struct_0(X1))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_11020])).

cnf(c_71616,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK2(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(X0) != sK2(u1_struct_0(X1))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_24047])).

cnf(c_71621,plain,
    ( u1_struct_0(X0) != sK2(u1_struct_0(X1))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK2(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71616])).

cnf(c_71623,plain,
    ( u1_struct_0(sK7) != sK2(u1_struct_0(sK7))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7))
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71621])).

cnf(c_89493,plain,
    ( r2_hidden(sK1(u1_struct_0(sK7),u1_struct_0(sK7),sK8),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_89307,c_39,c_38,c_36,c_35,c_78,c_521,c_523,c_531,c_1996,c_1997,c_2180,c_2768,c_2778,c_3456,c_3674,c_4613,c_6027,c_7235,c_7633,c_15682,c_22644,c_71623])).

cnf(c_89502,plain,
    ( u1_struct_0(sK7) = sK8
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_88710,c_89493])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89502,c_71623,c_22644,c_15682,c_7633,c_7342,c_7235,c_4613,c_3456,c_2778,c_2180,c_1997,c_1996,c_531,c_521,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:34:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.77/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.77/3.50  
% 23.77/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.77/3.50  
% 23.77/3.50  ------  iProver source info
% 23.77/3.50  
% 23.77/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.77/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.77/3.50  git: non_committed_changes: false
% 23.77/3.50  git: last_make_outside_of_git: false
% 23.77/3.50  
% 23.77/3.50  ------ 
% 23.77/3.50  ------ Parsing...
% 23.77/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.77/3.50  
% 23.77/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.77/3.50  ------ Proving...
% 23.77/3.50  ------ Problem Properties 
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  clauses                                 43
% 23.77/3.50  conjectures                             9
% 23.77/3.50  EPR                                     10
% 23.77/3.50  Horn                                    29
% 23.77/3.50  unary                                   10
% 23.77/3.50  binary                                  10
% 23.77/3.50  lits                                    133
% 23.77/3.50  lits eq                                 8
% 23.77/3.50  fd_pure                                 0
% 23.77/3.50  fd_pseudo                               0
% 23.77/3.50  fd_cond                                 0
% 23.77/3.50  fd_pseudo_cond                          7
% 23.77/3.50  AC symbols                              0
% 23.77/3.50  
% 23.77/3.50  ------ Input Options Time Limit: Unbounded
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  ------ 
% 23.77/3.50  Current options:
% 23.77/3.50  ------ 
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  ------ Proving...
% 23.77/3.50  
% 23.77/3.50  
% 23.77/3.50  % SZS status Theorem for theBenchmark.p
% 23.77/3.50  
% 23.77/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.77/3.50  
% 23.77/3.50  fof(f4,axiom,(
% 23.77/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f27,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(ennf_transformation,[],[f4])).
% 23.77/3.50  
% 23.77/3.50  fof(f28,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(flattening,[],[f27])).
% 23.77/3.50  
% 23.77/3.50  fof(f51,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(nnf_transformation,[],[f28])).
% 23.77/3.50  
% 23.77/3.50  fof(f52,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(flattening,[],[f51])).
% 23.77/3.50  
% 23.77/3.50  fof(f53,plain,(
% 23.77/3.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f54,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 23.77/3.50  
% 23.77/3.50  fof(f81,plain,(
% 23.77/3.50    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.77/3.50    inference(cnf_transformation,[],[f54])).
% 23.77/3.50  
% 23.77/3.50  fof(f1,axiom,(
% 23.77/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f20,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 23.77/3.50    inference(unused_predicate_definition_removal,[],[f1])).
% 23.77/3.50  
% 23.77/3.50  fof(f25,plain,(
% 23.77/3.50    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 23.77/3.50    inference(ennf_transformation,[],[f20])).
% 23.77/3.50  
% 23.77/3.50  fof(f49,plain,(
% 23.77/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f50,plain,(
% 23.77/3.50    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f49])).
% 23.77/3.50  
% 23.77/3.50  fof(f77,plain,(
% 23.77/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f50])).
% 23.77/3.50  
% 23.77/3.50  fof(f3,axiom,(
% 23.77/3.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f80,plain,(
% 23.77/3.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 23.77/3.50    inference(cnf_transformation,[],[f3])).
% 23.77/3.50  
% 23.77/3.50  fof(f8,axiom,(
% 23.77/3.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f32,plain,(
% 23.77/3.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 23.77/3.50    inference(ennf_transformation,[],[f8])).
% 23.77/3.50  
% 23.77/3.50  fof(f33,plain,(
% 23.77/3.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.77/3.50    inference(flattening,[],[f32])).
% 23.77/3.50  
% 23.77/3.50  fof(f88,plain,(
% 23.77/3.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f33])).
% 23.77/3.50  
% 23.77/3.50  fof(f2,axiom,(
% 23.77/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f26,plain,(
% 23.77/3.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(ennf_transformation,[],[f2])).
% 23.77/3.50  
% 23.77/3.50  fof(f79,plain,(
% 23.77/3.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.77/3.50    inference(cnf_transformation,[],[f26])).
% 23.77/3.50  
% 23.77/3.50  fof(f78,plain,(
% 23.77/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f50])).
% 23.77/3.50  
% 23.77/3.50  fof(f10,axiom,(
% 23.77/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f35,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(ennf_transformation,[],[f10])).
% 23.77/3.50  
% 23.77/3.50  fof(f36,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(flattening,[],[f35])).
% 23.77/3.50  
% 23.77/3.50  fof(f57,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(nnf_transformation,[],[f36])).
% 23.77/3.50  
% 23.77/3.50  fof(f58,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(rectify,[],[f57])).
% 23.77/3.50  
% 23.77/3.50  fof(f59,plain,(
% 23.77/3.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f60,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 23.77/3.50  
% 23.77/3.50  fof(f92,plain,(
% 23.77/3.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f60])).
% 23.77/3.50  
% 23.77/3.50  fof(f9,axiom,(
% 23.77/3.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f34,plain,(
% 23.77/3.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 23.77/3.50    inference(ennf_transformation,[],[f9])).
% 23.77/3.50  
% 23.77/3.50  fof(f89,plain,(
% 23.77/3.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f34])).
% 23.77/3.50  
% 23.77/3.50  fof(f12,axiom,(
% 23.77/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f38,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(ennf_transformation,[],[f12])).
% 23.77/3.50  
% 23.77/3.50  fof(f39,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(flattening,[],[f38])).
% 23.77/3.50  
% 23.77/3.50  fof(f61,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(nnf_transformation,[],[f39])).
% 23.77/3.50  
% 23.77/3.50  fof(f62,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(flattening,[],[f61])).
% 23.77/3.50  
% 23.77/3.50  fof(f63,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(rectify,[],[f62])).
% 23.77/3.50  
% 23.77/3.50  fof(f64,plain,(
% 23.77/3.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f65,plain,(
% 23.77/3.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f63,f64])).
% 23.77/3.50  
% 23.77/3.50  fof(f96,plain,(
% 23.77/3.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f65])).
% 23.77/3.50  
% 23.77/3.50  fof(f120,plain,(
% 23.77/3.50    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(equality_resolution,[],[f96])).
% 23.77/3.50  
% 23.77/3.50  fof(f13,axiom,(
% 23.77/3.50    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f40,plain,(
% 23.77/3.50    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(ennf_transformation,[],[f13])).
% 23.77/3.50  
% 23.77/3.50  fof(f100,plain,(
% 23.77/3.50    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f40])).
% 23.77/3.50  
% 23.77/3.50  fof(f18,conjecture,(
% 23.77/3.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f19,negated_conjecture,(
% 23.77/3.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 23.77/3.50    inference(negated_conjecture,[],[f18])).
% 23.77/3.50  
% 23.77/3.50  fof(f21,plain,(
% 23.77/3.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 23.77/3.50    inference(pure_predicate_removal,[],[f19])).
% 23.77/3.50  
% 23.77/3.50  fof(f22,plain,(
% 23.77/3.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 23.77/3.50    inference(pure_predicate_removal,[],[f21])).
% 23.77/3.50  
% 23.77/3.50  fof(f23,plain,(
% 23.77/3.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 23.77/3.50    inference(pure_predicate_removal,[],[f22])).
% 23.77/3.50  
% 23.77/3.50  fof(f47,plain,(
% 23.77/3.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 23.77/3.50    inference(ennf_transformation,[],[f23])).
% 23.77/3.50  
% 23.77/3.50  fof(f48,plain,(
% 23.77/3.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 23.77/3.50    inference(flattening,[],[f47])).
% 23.77/3.50  
% 23.77/3.50  fof(f72,plain,(
% 23.77/3.50    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 23.77/3.50    inference(nnf_transformation,[],[f48])).
% 23.77/3.50  
% 23.77/3.50  fof(f73,plain,(
% 23.77/3.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 23.77/3.50    inference(flattening,[],[f72])).
% 23.77/3.50  
% 23.77/3.50  fof(f75,plain,(
% 23.77/3.50    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK8) | ~v1_subset_1(sK8,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK8) | v1_subset_1(sK8,u1_struct_0(X0))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK8,X0) & ~v1_xboole_0(sK8))) )),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f74,plain,(
% 23.77/3.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK7),X1) | ~v1_subset_1(X1,u1_struct_0(sK7))) & (~r2_hidden(k3_yellow_0(sK7),X1) | v1_subset_1(X1,u1_struct_0(sK7))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) & v13_waybel_0(X1,sK7) & ~v1_xboole_0(X1)) & l1_orders_2(sK7) & v1_yellow_0(sK7) & v5_orders_2(sK7) & ~v2_struct_0(sK7))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f76,plain,(
% 23.77/3.50    ((r2_hidden(k3_yellow_0(sK7),sK8) | ~v1_subset_1(sK8,u1_struct_0(sK7))) & (~r2_hidden(k3_yellow_0(sK7),sK8) | v1_subset_1(sK8,u1_struct_0(sK7))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) & v13_waybel_0(sK8,sK7) & ~v1_xboole_0(sK8)) & l1_orders_2(sK7) & v1_yellow_0(sK7) & v5_orders_2(sK7) & ~v2_struct_0(sK7)),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f73,f75,f74])).
% 23.77/3.50  
% 23.77/3.50  fof(f117,plain,(
% 23.77/3.50    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f16,axiom,(
% 23.77/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f44,plain,(
% 23.77/3.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(ennf_transformation,[],[f16])).
% 23.77/3.50  
% 23.77/3.50  fof(f45,plain,(
% 23.77/3.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(flattening,[],[f44])).
% 23.77/3.50  
% 23.77/3.50  fof(f66,plain,(
% 23.77/3.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(nnf_transformation,[],[f45])).
% 23.77/3.50  
% 23.77/3.50  fof(f67,plain,(
% 23.77/3.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(rectify,[],[f66])).
% 23.77/3.50  
% 23.77/3.50  fof(f69,plain,(
% 23.77/3.50    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK6(X0,X1),X1) & r1_orders_2(X0,X2,sK6(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))) )),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f68,plain,(
% 23.77/3.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK5(X0,X1),X3) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f70,plain,(
% 23.77/3.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK6(X0,X1),X1) & r1_orders_2(X0,sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f67,f69,f68])).
% 23.77/3.50  
% 23.77/3.50  fof(f103,plain,(
% 23.77/3.50    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f70])).
% 23.77/3.50  
% 23.77/3.50  fof(f114,plain,(
% 23.77/3.50    l1_orders_2(sK7)),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f116,plain,(
% 23.77/3.50    v13_waybel_0(sK8,sK7)),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f11,axiom,(
% 23.77/3.50    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f37,plain,(
% 23.77/3.50    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(ennf_transformation,[],[f11])).
% 23.77/3.50  
% 23.77/3.50  fof(f94,plain,(
% 23.77/3.50    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f37])).
% 23.77/3.50  
% 23.77/3.50  fof(f111,plain,(
% 23.77/3.50    ~v2_struct_0(sK7)),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f112,plain,(
% 23.77/3.50    v5_orders_2(sK7)),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f113,plain,(
% 23.77/3.50    v1_yellow_0(sK7)),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f119,plain,(
% 23.77/3.50    r2_hidden(k3_yellow_0(sK7),sK8) | ~v1_subset_1(sK8,u1_struct_0(sK7))),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f15,axiom,(
% 23.77/3.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f24,plain,(
% 23.77/3.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 23.77/3.50    inference(pure_predicate_removal,[],[f15])).
% 23.77/3.50  
% 23.77/3.50  fof(f42,plain,(
% 23.77/3.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 23.77/3.50    inference(ennf_transformation,[],[f24])).
% 23.77/3.50  
% 23.77/3.50  fof(f43,plain,(
% 23.77/3.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 23.77/3.50    inference(flattening,[],[f42])).
% 23.77/3.50  
% 23.77/3.50  fof(f102,plain,(
% 23.77/3.50    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f43])).
% 23.77/3.50  
% 23.77/3.50  fof(f17,axiom,(
% 23.77/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f46,plain,(
% 23.77/3.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(ennf_transformation,[],[f17])).
% 23.77/3.50  
% 23.77/3.50  fof(f71,plain,(
% 23.77/3.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(nnf_transformation,[],[f46])).
% 23.77/3.50  
% 23.77/3.50  fof(f110,plain,(
% 23.77/3.50    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.77/3.50    inference(cnf_transformation,[],[f71])).
% 23.77/3.50  
% 23.77/3.50  fof(f115,plain,(
% 23.77/3.50    ~v1_xboole_0(sK8)),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f118,plain,(
% 23.77/3.50    ~r2_hidden(k3_yellow_0(sK7),sK8) | v1_subset_1(sK8,u1_struct_0(sK7))),
% 23.77/3.50    inference(cnf_transformation,[],[f76])).
% 23.77/3.50  
% 23.77/3.50  fof(f14,axiom,(
% 23.77/3.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f41,plain,(
% 23.77/3.50    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 23.77/3.50    inference(ennf_transformation,[],[f14])).
% 23.77/3.50  
% 23.77/3.50  fof(f101,plain,(
% 23.77/3.50    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f41])).
% 23.77/3.50  
% 23.77/3.50  fof(f7,axiom,(
% 23.77/3.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f30,plain,(
% 23.77/3.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 23.77/3.50    inference(ennf_transformation,[],[f7])).
% 23.77/3.50  
% 23.77/3.50  fof(f31,plain,(
% 23.77/3.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 23.77/3.50    inference(flattening,[],[f30])).
% 23.77/3.50  
% 23.77/3.50  fof(f87,plain,(
% 23.77/3.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f31])).
% 23.77/3.50  
% 23.77/3.50  fof(f83,plain,(
% 23.77/3.50    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.77/3.50    inference(cnf_transformation,[],[f54])).
% 23.77/3.50  
% 23.77/3.50  fof(f5,axiom,(
% 23.77/3.50    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.77/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.77/3.50  
% 23.77/3.50  fof(f55,plain,(
% 23.77/3.50    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 23.77/3.50    introduced(choice_axiom,[])).
% 23.77/3.50  
% 23.77/3.50  fof(f56,plain,(
% 23.77/3.50    ! [X0] : (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 23.77/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f55])).
% 23.77/3.50  
% 23.77/3.50  fof(f84,plain,(
% 23.77/3.50    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 23.77/3.50    inference(cnf_transformation,[],[f56])).
% 23.77/3.50  
% 23.77/3.50  fof(f85,plain,(
% 23.77/3.50    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 23.77/3.50    inference(cnf_transformation,[],[f56])).
% 23.77/3.50  
% 23.77/3.50  cnf(c_6,plain,
% 23.77/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.77/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.77/3.50      | m1_subset_1(sK1(X1,X0,X2),X1)
% 23.77/3.50      | X2 = X0 ),
% 23.77/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1516,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 23.77/3.50      | m1_subset_1(sK1(X2,X1,X0),X2) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1,plain,
% 23.77/3.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.77/3.50      inference(cnf_transformation,[],[f77]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1521,plain,
% 23.77/3.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.77/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_3,plain,
% 23.77/3.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 23.77/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1519,plain,
% 23.77/3.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_11,plain,
% 23.77/3.50      ( m1_subset_1(X0,X1)
% 23.77/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.77/3.50      | ~ r2_hidden(X0,X2) ),
% 23.77/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1511,plain,
% 23.77/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.77/3.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 23.77/3.50      | r2_hidden(X0,X2) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_3619,plain,
% 23.77/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.77/3.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1519,c_1511]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_5378,plain,
% 23.77/3.50      ( m1_subset_1(sK0(k1_xboole_0,X0),X1) = iProver_top
% 23.77/3.50      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1521,c_3619]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_2,plain,
% 23.77/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.77/3.50      | ~ r2_hidden(X2,X0)
% 23.77/3.50      | r2_hidden(X2,X1) ),
% 23.77/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_2907,plain,
% 23.77/3.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 23.77/3.50      inference(resolution,[status(thm)],[c_2,c_3]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_3321,plain,
% 23.77/3.50      ( r2_hidden(sK0(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0) ),
% 23.77/3.50      inference(resolution,[status(thm)],[c_2907,c_1]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_0,plain,
% 23.77/3.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.77/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_3643,plain,
% 23.77/3.50      ( r1_tarski(k1_xboole_0,X0) ),
% 23.77/3.50      inference(resolution,[status(thm)],[c_3321,c_0]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_3644,plain,
% 23.77/3.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_3643]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_10923,plain,
% 23.77/3.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.77/3.50      inference(global_propositional_subsumption,
% 23.77/3.50                [status(thm)],
% 23.77/3.50                [c_5378,c_3644]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_14,plain,
% 23.77/3.50      ( r2_lattice3(X0,X1,X2)
% 23.77/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.77/3.50      | r2_hidden(sK3(X0,X1,X2),X1)
% 23.77/3.50      | ~ l1_orders_2(X0) ),
% 23.77/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1508,plain,
% 23.77/3.50      ( r2_lattice3(X0,X1,X2) = iProver_top
% 23.77/3.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_12,plain,
% 23.77/3.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 23.77/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1510,plain,
% 23.77/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.77/3.50      | r1_tarski(X1,X0) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_5226,plain,
% 23.77/3.50      ( r2_lattice3(X0,X1,X2) = iProver_top
% 23.77/3.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | r1_tarski(X1,sK3(X0,X1,X2)) != iProver_top
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1508,c_1510]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_10929,plain,
% 23.77/3.50      ( r2_lattice3(X0,k1_xboole_0,X1) = iProver_top
% 23.77/3.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_10923,c_5226]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_76074,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r2_lattice3(X2,k1_xboole_0,sK1(u1_struct_0(X2),X0,X1)) = iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 23.77/3.50      | l1_orders_2(X2) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1516,c_10929]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_21,plain,
% 23.77/3.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 23.77/3.50      | ~ r2_lattice3(X0,X1,X2)
% 23.77/3.50      | ~ r1_yellow_0(X0,X1)
% 23.77/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.77/3.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 23.77/3.50      | ~ l1_orders_2(X0) ),
% 23.77/3.50      inference(cnf_transformation,[],[f120]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_23,plain,
% 23.77/3.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 23.77/3.50      | ~ l1_orders_2(X0) ),
% 23.77/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_460,plain,
% 23.77/3.50      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.77/3.50      | ~ r1_yellow_0(X0,X1)
% 23.77/3.50      | ~ r2_lattice3(X0,X1,X2)
% 23.77/3.50      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 23.77/3.50      | ~ l1_orders_2(X0) ),
% 23.77/3.50      inference(global_propositional_subsumption,
% 23.77/3.50                [status(thm)],
% 23.77/3.50                [c_21,c_23]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_461,plain,
% 23.77/3.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 23.77/3.50      | ~ r2_lattice3(X0,X1,X2)
% 23.77/3.50      | ~ r1_yellow_0(X0,X1)
% 23.77/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.77/3.50      | ~ l1_orders_2(X0) ),
% 23.77/3.50      inference(renaming,[status(thm)],[c_460]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1480,plain,
% 23.77/3.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2) = iProver_top
% 23.77/3.50      | r2_lattice3(X0,X1,X2) != iProver_top
% 23.77/3.50      | r1_yellow_0(X0,X1) != iProver_top
% 23.77/3.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_36,negated_conjecture,
% 23.77/3.50      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 23.77/3.50      inference(cnf_transformation,[],[f117]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1488,plain,
% 23.77/3.50      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_31,plain,
% 23.77/3.50      ( ~ r1_orders_2(X0,X1,X2)
% 23.77/3.50      | ~ v13_waybel_0(X3,X0)
% 23.77/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.77/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.77/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.50      | ~ r2_hidden(X1,X3)
% 23.77/3.50      | r2_hidden(X2,X3)
% 23.77/3.50      | ~ l1_orders_2(X0) ),
% 23.77/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1493,plain,
% 23.77/3.50      ( r1_orders_2(X0,X1,X2) != iProver_top
% 23.77/3.50      | v13_waybel_0(X3,X0) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.77/3.50      | r2_hidden(X1,X3) != iProver_top
% 23.77/3.50      | r2_hidden(X2,X3) = iProver_top
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1781,plain,
% 23.77/3.50      ( r1_orders_2(X0,X1,X2) != iProver_top
% 23.77/3.50      | v13_waybel_0(X3,X0) != iProver_top
% 23.77/3.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 23.77/3.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.77/3.50      | r2_hidden(X1,X3) != iProver_top
% 23.77/3.50      | r2_hidden(X2,X3) = iProver_top
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(forward_subsumption_resolution,
% 23.77/3.50                [status(thm)],
% 23.77/3.50                [c_1493,c_1511]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_8847,plain,
% 23.77/3.50      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 23.77/3.50      | v13_waybel_0(sK8,sK7) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | r2_hidden(X0,sK8) != iProver_top
% 23.77/3.50      | r2_hidden(X1,sK8) = iProver_top
% 23.77/3.50      | l1_orders_2(sK7) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1488,c_1781]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_39,negated_conjecture,
% 23.77/3.50      ( l1_orders_2(sK7) ),
% 23.77/3.50      inference(cnf_transformation,[],[f114]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_46,plain,
% 23.77/3.50      ( l1_orders_2(sK7) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_37,negated_conjecture,
% 23.77/3.50      ( v13_waybel_0(sK8,sK7) ),
% 23.77/3.50      inference(cnf_transformation,[],[f116]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_48,plain,
% 23.77/3.50      ( v13_waybel_0(sK8,sK7) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_9358,plain,
% 23.77/3.50      ( r2_hidden(X1,sK8) = iProver_top
% 23.77/3.50      | r2_hidden(X0,sK8) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | r1_orders_2(sK7,X0,X1) != iProver_top ),
% 23.77/3.50      inference(global_propositional_subsumption,
% 23.77/3.50                [status(thm)],
% 23.77/3.50                [c_8847,c_46,c_48]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_9359,plain,
% 23.77/3.50      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | r2_hidden(X0,sK8) != iProver_top
% 23.77/3.50      | r2_hidden(X1,sK8) = iProver_top ),
% 23.77/3.50      inference(renaming,[status(thm)],[c_9358]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_9372,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r1_orders_2(sK7,X2,sK1(u1_struct_0(sK7),X0,X1)) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | r2_hidden(X2,sK8) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1516,c_9359]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_11264,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X1,X0)) != iProver_top
% 23.77/3.50      | r1_yellow_0(sK7,X2) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(sK1(u1_struct_0(sK7),X1,X0),u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
% 23.77/3.50      | r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top
% 23.77/3.50      | l1_orders_2(sK7) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1480,c_9372]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_18312,plain,
% 23.77/3.50      ( r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
% 23.77/3.50      | m1_subset_1(sK1(u1_struct_0(sK7),X1,X0),u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | r1_yellow_0(sK7,X2) != iProver_top
% 23.77/3.50      | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X1,X0)) != iProver_top
% 23.77/3.50      | X0 = X1 ),
% 23.77/3.50      inference(global_propositional_subsumption,
% 23.77/3.50                [status(thm)],
% 23.77/3.50                [c_11264,c_46]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_18313,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X1,X0)) != iProver_top
% 23.77/3.50      | r1_yellow_0(sK7,X2) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(sK1(u1_struct_0(sK7),X1,X0),u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
% 23.77/3.50      | r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top ),
% 23.77/3.50      inference(renaming,[status(thm)],[c_18312]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_18324,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r2_lattice3(sK7,X2,sK1(u1_struct_0(sK7),X0,X1)) != iProver_top
% 23.77/3.50      | r1_yellow_0(sK7,X2) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top
% 23.77/3.50      | r2_hidden(k1_yellow_0(sK7,X2),sK8) != iProver_top ),
% 23.77/3.50      inference(forward_subsumption_resolution,
% 23.77/3.50                [status(thm)],
% 23.77/3.50                [c_18313,c_1516]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_87845,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r1_yellow_0(sK7,k1_xboole_0) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top
% 23.77/3.50      | r2_hidden(k1_yellow_0(sK7,k1_xboole_0),sK8) != iProver_top
% 23.77/3.50      | l1_orders_2(sK7) != iProver_top ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_76074,c_18324]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1485,plain,
% 23.77/3.50      ( l1_orders_2(sK7) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_17,plain,
% 23.77/3.50      ( ~ l1_orders_2(X0)
% 23.77/3.50      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 23.77/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_1505,plain,
% 23.77/3.50      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 23.77/3.50      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_2260,plain,
% 23.77/3.50      ( k1_yellow_0(sK7,k1_xboole_0) = k3_yellow_0(sK7) ),
% 23.77/3.50      inference(superposition,[status(thm)],[c_1485,c_1505]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_87925,plain,
% 23.77/3.50      ( X0 = X1
% 23.77/3.50      | r1_yellow_0(sK7,k1_xboole_0) != iProver_top
% 23.77/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.50      | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top
% 23.77/3.50      | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top
% 23.77/3.50      | l1_orders_2(sK7) != iProver_top ),
% 23.77/3.50      inference(light_normalisation,[status(thm)],[c_87845,c_2260]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_42,negated_conjecture,
% 23.77/3.50      ( ~ v2_struct_0(sK7) ),
% 23.77/3.50      inference(cnf_transformation,[],[f111]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_43,plain,
% 23.77/3.50      ( v2_struct_0(sK7) != iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_41,negated_conjecture,
% 23.77/3.50      ( v5_orders_2(sK7) ),
% 23.77/3.50      inference(cnf_transformation,[],[f112]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_44,plain,
% 23.77/3.50      ( v5_orders_2(sK7) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_40,negated_conjecture,
% 23.77/3.50      ( v1_yellow_0(sK7) ),
% 23.77/3.50      inference(cnf_transformation,[],[f113]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_45,plain,
% 23.77/3.50      ( v1_yellow_0(sK7) = iProver_top ),
% 23.77/3.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_34,negated_conjecture,
% 23.77/3.50      ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.50      | r2_hidden(k3_yellow_0(sK7),sK8) ),
% 23.77/3.50      inference(cnf_transformation,[],[f119]) ).
% 23.77/3.50  
% 23.77/3.50  cnf(c_51,plain,
% 23.77/3.50      ( v1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 23.77/3.50      | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_25,plain,
% 23.77/3.51      ( r1_yellow_0(X0,k1_xboole_0)
% 23.77/3.51      | v2_struct_0(X0)
% 23.77/3.51      | ~ v5_orders_2(X0)
% 23.77/3.51      | ~ v1_yellow_0(X0)
% 23.77/3.51      | ~ l1_orders_2(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f102]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_74,plain,
% 23.77/3.51      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 23.77/3.51      | v2_struct_0(X0) = iProver_top
% 23.77/3.51      | v5_orders_2(X0) != iProver_top
% 23.77/3.51      | v1_yellow_0(X0) != iProver_top
% 23.77/3.51      | l1_orders_2(X0) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_76,plain,
% 23.77/3.51      ( r1_yellow_0(sK7,k1_xboole_0) = iProver_top
% 23.77/3.51      | v2_struct_0(sK7) = iProver_top
% 23.77/3.51      | v5_orders_2(sK7) != iProver_top
% 23.77/3.51      | v1_yellow_0(sK7) != iProver_top
% 23.77/3.51      | l1_orders_2(sK7) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_74]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_32,plain,
% 23.77/3.51      ( v1_subset_1(X0,X1)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.77/3.51      | X0 = X1 ),
% 23.77/3.51      inference(cnf_transformation,[],[f110]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_506,plain,
% 23.77/3.51      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3049,plain,
% 23.77/3.51      ( v1_subset_1(X0,X1)
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.77/3.51      | ~ l1_orders_2(X1)
% 23.77/3.51      | l1_orders_2(X0) ),
% 23.77/3.51      inference(resolution,[status(thm)],[c_32,c_506]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7202,plain,
% 23.77/3.51      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | ~ l1_orders_2(u1_struct_0(sK7))
% 23.77/3.51      | l1_orders_2(sK8) ),
% 23.77/3.51      inference(resolution,[status(thm)],[c_3049,c_36]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_38,negated_conjecture,
% 23.77/3.51      ( ~ v1_xboole_0(sK8) ),
% 23.77/3.51      inference(cnf_transformation,[],[f115]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_35,negated_conjecture,
% 23.77/3.51      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 23.77/3.51      inference(cnf_transformation,[],[f118]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24,plain,
% 23.77/3.51      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 23.77/3.51      | ~ l1_orders_2(X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f101]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_78,plain,
% 23.77/3.51      ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 23.77/3.51      | ~ l1_orders_2(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_24]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_507,plain,
% 23.77/3.51      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_523,plain,
% 23.77/3.51      ( k3_yellow_0(sK7) = k3_yellow_0(sK7) | sK7 != sK7 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_507]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_496,plain,( X0 = X0 ),theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_531,plain,
% 23.77/3.51      ( sK7 = sK7 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_496]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2357,plain,
% 23.77/3.51      ( v1_subset_1(X0,u1_struct_0(X1))
% 23.77/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | X0 = u1_struct_0(X1) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_32]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2768,plain,
% 23.77/3.51      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 23.77/3.51      | sK8 = u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2357]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_500,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2047,plain,
% 23.77/3.51      ( m1_subset_1(X0,X1)
% 23.77/3.51      | ~ m1_subset_1(k3_yellow_0(X2),u1_struct_0(X2))
% 23.77/3.51      | X0 != k3_yellow_0(X2)
% 23.77/3.51      | X1 != u1_struct_0(X2) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_500]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3198,plain,
% 23.77/3.51      ( m1_subset_1(X0,sK8)
% 23.77/3.51      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 23.77/3.51      | X0 != k3_yellow_0(sK7)
% 23.77/3.51      | sK8 != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2047]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3671,plain,
% 23.77/3.51      ( m1_subset_1(k3_yellow_0(X0),sK8)
% 23.77/3.51      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 23.77/3.51      | k3_yellow_0(X0) != k3_yellow_0(sK7)
% 23.77/3.51      | sK8 != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_3198]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3674,plain,
% 23.77/3.51      ( ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 23.77/3.51      | m1_subset_1(k3_yellow_0(sK7),sK8)
% 23.77/3.51      | k3_yellow_0(sK7) != k3_yellow_0(sK7)
% 23.77/3.51      | sK8 != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_3671]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_10,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.77/3.51      inference(cnf_transformation,[],[f87]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6027,plain,
% 23.77/3.51      ( ~ m1_subset_1(k3_yellow_0(sK7),sK8)
% 23.77/3.51      | r2_hidden(k3_yellow_0(sK7),sK8)
% 23.77/3.51      | v1_xboole_0(sK8) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_10]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7342,plain,
% 23.77/3.51      ( v1_subset_1(sK8,u1_struct_0(sK7)) ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_7202,c_39,c_38,c_36,c_35,c_78,c_523,c_531,c_2768,
% 23.77/3.51                 c_3674,c_6027]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7344,plain,
% 23.77/3.51      ( v1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_7342]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_88709,plain,
% 23.77/3.51      ( X0 = X1
% 23.77/3.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_87925,c_43,c_44,c_45,c_46,c_51,c_76,c_7344]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_88710,plain,
% 23.77/3.51      ( X0 = X1
% 23.77/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(u1_struct_0(sK7),X0,X1),sK8) = iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_88709]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_1520,plain,
% 23.77/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.77/3.51      | r2_hidden(X2,X0) != iProver_top
% 23.77/3.51      | r2_hidden(X2,X1) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3962,plain,
% 23.77/3.51      ( r2_hidden(X0,u1_struct_0(sK7)) = iProver_top
% 23.77/3.51      | r2_hidden(X0,sK8) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_1488,c_1520]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_4,plain,
% 23.77/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.77/3.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.77/3.51      | ~ r2_hidden(sK1(X1,X0,X2),X2)
% 23.77/3.51      | ~ r2_hidden(sK1(X1,X0,X2),X0)
% 23.77/3.51      | X2 = X0 ),
% 23.77/3.51      inference(cnf_transformation,[],[f83]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_1518,plain,
% 23.77/3.51      ( X0 = X1
% 23.77/3.51      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 23.77/3.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(X2,X1,X0),X0) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(X2,X1,X0),X1) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_88720,plain,
% 23.77/3.51      ( sK8 = X0
% 23.77/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(u1_struct_0(sK7),X0,sK8),X0) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_88710,c_1518]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_49,plain,
% 23.77/3.51      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_89294,plain,
% 23.77/3.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | sK8 = X0
% 23.77/3.51      | r2_hidden(sK1(u1_struct_0(sK7),X0,sK8),X0) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_88720,c_49]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_89295,plain,
% 23.77/3.51      ( sK8 = X0
% 23.77/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(u1_struct_0(sK7),X0,sK8),X0) != iProver_top ),
% 23.77/3.51      inference(renaming,[status(thm)],[c_89294]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_89307,plain,
% 23.77/3.51      ( u1_struct_0(sK7) = sK8
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | r2_hidden(sK1(u1_struct_0(sK7),u1_struct_0(sK7),sK8),sK8) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_3962,c_89295]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_505,plain,
% 23.77/3.51      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_521,plain,
% 23.77/3.51      ( u1_struct_0(sK7) = u1_struct_0(sK7) | sK7 != sK7 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_505]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_8,plain,
% 23.77/3.51      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
% 23.77/3.51      inference(cnf_transformation,[],[f84]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_1990,plain,
% 23.77/3.51      ( m1_subset_1(sK2(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_8]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_1996,plain,
% 23.77/3.51      ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_1990]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_1995,plain,
% 23.77/3.51      ( m1_subset_1(sK2(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_1990]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_1997,plain,
% 23.77/3.51      ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_1995]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2180,plain,
% 23.77/3.51      ( sK8 = sK8 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_496]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2776,plain,
% 23.77/3.51      ( v1_subset_1(sK2(u1_struct_0(X0)),u1_struct_0(X0))
% 23.77/3.51      | ~ m1_subset_1(sK2(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 23.77/3.51      | sK2(u1_struct_0(X0)) = u1_struct_0(X0) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2357]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2778,plain,
% 23.77/3.51      ( v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(sK7))
% 23.77/3.51      | ~ m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
% 23.77/3.51      | sK2(u1_struct_0(sK7)) = u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2776]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_499,plain,
% 23.77/3.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2542,plain,
% 23.77/3.51      ( X0 != u1_struct_0(sK7)
% 23.77/3.51      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK7)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_499]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3454,plain,
% 23.77/3.51      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(sK7)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2542]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3456,plain,
% 23.77/3.51      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(sK7)) = k1_zfmisc_1(u1_struct_0(sK7)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_3454]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_497,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2162,plain,
% 23.77/3.51      ( X0 != X1 | X0 = sK8 | sK8 != X1 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_497]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3207,plain,
% 23.77/3.51      ( X0 != u1_struct_0(sK7) | X0 = sK8 | sK8 != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2162]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_4613,plain,
% 23.77/3.51      ( sK2(u1_struct_0(sK7)) != u1_struct_0(sK7)
% 23.77/3.51      | sK2(u1_struct_0(sK7)) = sK8
% 23.77/3.51      | sK8 != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_3207]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7,plain,
% 23.77/3.51      ( ~ v1_subset_1(sK2(X0),X0) ),
% 23.77/3.51      inference(cnf_transformation,[],[f85]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7235,plain,
% 23.77/3.51      ( ~ v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_7]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2560,plain,
% 23.77/3.51      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_497]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_4179,plain,
% 23.77/3.51      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2560]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_7633,plain,
% 23.77/3.51      ( u1_struct_0(sK7) != sK8 | sK8 = u1_struct_0(sK7) | sK8 != sK8 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_4179]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_501,plain,
% 23.77/3.51      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.77/3.51      theory(equality) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_3458,plain,
% 23.77/3.51      ( v1_subset_1(X0,X1)
% 23.77/3.51      | ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | X1 != u1_struct_0(sK7)
% 23.77/3.51      | X0 != sK8 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_501]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_6777,plain,
% 23.77/3.51      ( v1_subset_1(X0,u1_struct_0(X1))
% 23.77/3.51      | ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | X0 != sK8
% 23.77/3.51      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_3458]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_15680,plain,
% 23.77/3.51      ( v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(X0))
% 23.77/3.51      | ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | u1_struct_0(X0) != u1_struct_0(sK7)
% 23.77/3.51      | sK2(u1_struct_0(sK7)) != sK8 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_6777]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_15682,plain,
% 23.77/3.51      ( v1_subset_1(sK2(u1_struct_0(sK7)),u1_struct_0(sK7))
% 23.77/3.51      | ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 23.77/3.51      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 23.77/3.51      | sK2(u1_struct_0(sK7)) != sK8 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_15680]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2321,plain,
% 23.77/3.51      ( X0 != X1 | X0 = sK2(X2) | sK2(X2) != X1 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_497]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_4354,plain,
% 23.77/3.51      ( u1_struct_0(X0) != X1
% 23.77/3.51      | u1_struct_0(X0) = sK2(X2)
% 23.77/3.51      | sK2(X2) != X1 ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2321]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_9645,plain,
% 23.77/3.51      ( u1_struct_0(X0) != u1_struct_0(X1)
% 23.77/3.51      | u1_struct_0(X0) = sK2(X2)
% 23.77/3.51      | sK2(X2) != u1_struct_0(X1) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_4354]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_22643,plain,
% 23.77/3.51      ( u1_struct_0(X0) != u1_struct_0(X1)
% 23.77/3.51      | u1_struct_0(X0) = sK2(u1_struct_0(X1))
% 23.77/3.51      | sK2(u1_struct_0(X1)) != u1_struct_0(X1) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_9645]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_22644,plain,
% 23.77/3.51      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 23.77/3.51      | u1_struct_0(sK7) = sK2(u1_struct_0(sK7))
% 23.77/3.51      | sK2(u1_struct_0(sK7)) != u1_struct_0(sK7) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_22643]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_2037,plain,
% 23.77/3.51      ( m1_subset_1(X0,X1)
% 23.77/3.51      | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
% 23.77/3.51      | X0 != sK2(X2)
% 23.77/3.51      | X1 != k1_zfmisc_1(X2) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_500]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_4337,plain,
% 23.77/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.77/3.51      | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
% 23.77/3.51      | X0 != sK2(X2)
% 23.77/3.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_2037]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_11020,plain,
% 23.77/3.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
% 23.77/3.51      | X0 != sK2(X2)
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_4337]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_24047,plain,
% 23.77/3.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 23.77/3.51      | ~ m1_subset_1(sK2(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | X0 != sK2(u1_struct_0(X1))
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_11020]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_71616,plain,
% 23.77/3.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 23.77/3.51      | ~ m1_subset_1(sK2(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
% 23.77/3.51      | u1_struct_0(X0) != sK2(u1_struct_0(X1))
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_24047]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_71621,plain,
% 23.77/3.51      ( u1_struct_0(X0) != sK2(u1_struct_0(X1))
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(X1))
% 23.77/3.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 23.77/3.51      | m1_subset_1(sK2(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top ),
% 23.77/3.51      inference(predicate_to_equality,[status(thm)],[c_71616]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_71623,plain,
% 23.77/3.51      ( u1_struct_0(sK7) != sK2(u1_struct_0(sK7))
% 23.77/3.51      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7))
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 23.77/3.51      | m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
% 23.77/3.51      inference(instantiation,[status(thm)],[c_71621]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_89493,plain,
% 23.77/3.51      ( r2_hidden(sK1(u1_struct_0(sK7),u1_struct_0(sK7),sK8),sK8) != iProver_top ),
% 23.77/3.51      inference(global_propositional_subsumption,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_89307,c_39,c_38,c_36,c_35,c_78,c_521,c_523,c_531,
% 23.77/3.51                 c_1996,c_1997,c_2180,c_2768,c_2778,c_3456,c_3674,c_4613,
% 23.77/3.51                 c_6027,c_7235,c_7633,c_15682,c_22644,c_71623]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(c_89502,plain,
% 23.77/3.51      ( u1_struct_0(sK7) = sK8
% 23.77/3.51      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 23.77/3.51      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
% 23.77/3.51      inference(superposition,[status(thm)],[c_88710,c_89493]) ).
% 23.77/3.51  
% 23.77/3.51  cnf(contradiction,plain,
% 23.77/3.51      ( $false ),
% 23.77/3.51      inference(minisat,
% 23.77/3.51                [status(thm)],
% 23.77/3.51                [c_89502,c_71623,c_22644,c_15682,c_7633,c_7342,c_7235,
% 23.77/3.51                 c_4613,c_3456,c_2778,c_2180,c_1997,c_1996,c_531,c_521,
% 23.77/3.51                 c_49]) ).
% 23.77/3.51  
% 23.77/3.51  
% 23.77/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.77/3.51  
% 23.77/3.51  ------                               Statistics
% 23.77/3.51  
% 23.77/3.51  ------ Selected
% 23.77/3.51  
% 23.77/3.51  total_time:                             2.922
% 23.77/3.51  
%------------------------------------------------------------------------------

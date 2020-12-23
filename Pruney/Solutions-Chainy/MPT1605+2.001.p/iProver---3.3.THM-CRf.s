%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:12 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 447 expanded)
%              Number of clauses        :  120 ( 182 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   29
%              Number of atoms          :  937 (1579 expanded)
%              Number of equality atoms :  229 ( 314 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f49,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f78,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6))
      & r2_hidden(k1_xboole_0,sK6)
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6))
    & r2_hidden(k1_xboole_0,sK6)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f78])).

fof(f120,plain,(
    r2_hidden(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f79])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f65,f66])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f112,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f115,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f74,plain,(
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
    inference(rectify,[],[f73])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f88,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f87,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f111,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f24,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f114,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f100,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f68])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f69,f70])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_yellow_0(X0)
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f121,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6)) ),
    inference(cnf_transformation,[],[f79])).

fof(f119,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_8112,plain,
    ( r2_hidden(k1_xboole_0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_8113,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8496,plain,
    ( m1_subset_1(k1_xboole_0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8112,c_8113])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8116,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8118,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8509,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8116,c_8118])).

cnf(c_17,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_32,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1461,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_1462,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r2_hidden(sK3(k2_yellow_1(X0),X1,X2),X1) ),
    inference(unflattening,[status(thm)],[c_1461])).

cnf(c_8092,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(sK3(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_36,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_8211,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r2_hidden(sK3(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8092,c_36])).

cnf(c_8660,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8211,c_8118])).

cnf(c_27,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_29,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_29])).

cnf(c_249,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_464,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_31,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | ~ v1_yellow_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_33,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_482,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_483,plain,
    ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( ~ v1_yellow_0(k2_yellow_1(X0))
    | r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_32])).

cnf(c_488,plain,
    ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_487])).

cnf(c_730,plain,
    ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ l1_orders_2(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | k2_yellow_1(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_464,c_488])).

cnf(c_731,plain,
    ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_735,plain,
    ( ~ v1_yellow_0(k2_yellow_1(X0))
    | r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_32])).

cnf(c_736,plain,
    ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_974,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v1_yellow_0(k2_yellow_1(X3))
    | ~ l1_orders_2(X0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X3)))
    | k2_yellow_1(X3) != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_249,c_736])).

cnf(c_975,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1)
    | ~ r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_32])).

cnf(c_980,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_8106,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_20,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1419,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_1420,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1419])).

cnf(c_8282,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8106,c_36,c_1420])).

cnf(c_37,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_540,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_541,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_32])).

cnf(c_546,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_545])).

cnf(c_703,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(X3)
    | v1_xboole_0(u1_struct_0(X3))
    | k2_yellow_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_464,c_546])).

cnf(c_704,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_32])).

cnf(c_709,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(renaming,[status(thm)],[c_708])).

cnf(c_1165,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(resolution,[status(thm)],[c_37,c_709])).

cnf(c_8100,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_8293,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8100,c_36])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_503,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_504,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | X2 = X1 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | X2 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_32])).

cnf(c_509,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | X2 = X1 ),
    inference(renaming,[status(thm)],[c_508])).

cnf(c_8107,plain,
    ( X0 = X1
    | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
    | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_8249,plain,
    ( X0 = X1
    | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
    | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
    | m1_subset_1(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8107,c_36])).

cnf(c_8903,plain,
    ( X0 = X1
    | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
    | m1_subset_1(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8293,c_8249])).

cnf(c_9367,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) != iProver_top
    | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8282,c_8903])).

cnf(c_30,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1362,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_1363,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_8099,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_8134,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8099,c_36])).

cnf(c_13972,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
    | k3_yellow_0(k2_yellow_1(X0)) = X1
    | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9367,c_8134])).

cnf(c_13973,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_13972])).

cnf(c_13983,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8660,c_13973])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_142,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14178,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k3_yellow_0(k2_yellow_1(X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13983,c_142])).

cnf(c_14179,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_14178])).

cnf(c_14187,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8509,c_14179])).

cnf(c_12,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1542,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_1543,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1542])).

cnf(c_8087,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_8235,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8087,c_36])).

cnf(c_8905,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8293,c_8235])).

cnf(c_14,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1512,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_1513,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1512])).

cnf(c_8089,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_8218,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8089,c_36])).

cnf(c_9493,plain,
    ( m1_subset_1(X2,X0) != iProver_top
    | r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8905,c_8218])).

cnf(c_9494,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9493])).

cnf(c_9501,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8509,c_9494])).

cnf(c_21,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1404,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_yellow_0(X0)
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_1405,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v1_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1404])).

cnf(c_8095,plain,
    ( r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_8197,plain,
    ( r1_lattice3(k2_yellow_1(X0),X0,X1) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8095,c_36])).

cnf(c_9529,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9501,c_8197])).

cnf(c_13,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1527,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_1528,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) ),
    inference(unflattening,[status(thm)],[c_1527])).

cnf(c_8088,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_8204,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8088,c_36])).

cnf(c_8620,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8204,c_8118])).

cnf(c_8763,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8620,c_8197])).

cnf(c_9953,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9529,c_8763])).

cnf(c_9954,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9953])).

cnf(c_14243,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14187,c_9954])).

cnf(c_14251,plain,
    ( k3_yellow_0(k2_yellow_1(sK6)) = k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8496,c_14243])).

cnf(c_2729,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_10911,plain,
    ( k3_yellow_0(k2_yellow_1(sK6)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2729])).

cnf(c_10912,plain,
    ( k3_yellow_0(k2_yellow_1(sK6)) != k1_xboole_0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK6))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10911])).

cnf(c_2728,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2763,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_42,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14251,c_10912,c_2763,c_142,c_39,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.70/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.98  
% 3.70/0.98  ------  iProver source info
% 3.70/0.98  
% 3.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.98  git: non_committed_changes: false
% 3.70/0.98  git: last_make_outside_of_git: false
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  ------ Parsing...
% 3.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  ------ Proving...
% 3.70/0.98  ------ Problem Properties 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  clauses                                 34
% 3.70/0.98  conjectures                             4
% 3.70/0.98  EPR                                     6
% 3.70/0.98  Horn                                    21
% 3.70/0.98  unary                                   9
% 3.70/0.98  binary                                  7
% 3.70/0.98  lits                                    100
% 3.70/0.98  lits eq                                 8
% 3.70/0.98  fd_pure                                 0
% 3.70/0.98  fd_pseudo                               0
% 3.70/0.98  fd_cond                                 0
% 3.70/0.98  fd_pseudo_cond                          4
% 3.70/0.98  AC symbols                              0
% 3.70/0.98  
% 3.70/0.98  ------ Input Options Time Limit: Unbounded
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.70/0.98  Current options:
% 3.70/0.98  ------ 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS status Theorem for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  fof(f21,conjecture,(
% 3.70/0.98    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f22,negated_conjecture,(
% 3.70/0.98    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 3.70/0.98    inference(negated_conjecture,[],[f21])).
% 3.70/0.98  
% 3.70/0.98  fof(f49,plain,(
% 3.70/0.98    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f22])).
% 3.70/0.98  
% 3.70/0.98  fof(f50,plain,(
% 3.70/0.98    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 3.70/0.98    inference(flattening,[],[f49])).
% 3.70/0.98  
% 3.70/0.98  fof(f78,plain,(
% 3.70/0.98    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6)) & r2_hidden(k1_xboole_0,sK6) & ~v1_xboole_0(sK6))),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f79,plain,(
% 3.70/0.98    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6)) & r2_hidden(k1_xboole_0,sK6) & ~v1_xboole_0(sK6)),
% 3.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f78])).
% 3.70/0.98  
% 3.70/0.98  fof(f120,plain,(
% 3.70/0.98    r2_hidden(k1_xboole_0,sK6)),
% 3.70/0.98    inference(cnf_transformation,[],[f79])).
% 3.70/0.98  
% 3.70/0.98  fof(f4,axiom,(
% 3.70/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f28,plain,(
% 3.70/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.70/0.98    inference(ennf_transformation,[],[f4])).
% 3.70/0.98  
% 3.70/0.98  fof(f86,plain,(
% 3.70/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f28])).
% 3.70/0.98  
% 3.70/0.98  fof(f2,axiom,(
% 3.70/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f27,plain,(
% 3.70/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.70/0.98    inference(ennf_transformation,[],[f2])).
% 3.70/0.98  
% 3.70/0.98  fof(f55,plain,(
% 3.70/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/0.98    inference(nnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f56,plain,(
% 3.70/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/0.98    inference(rectify,[],[f55])).
% 3.70/0.98  
% 3.70/0.98  fof(f57,plain,(
% 3.70/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f58,plain,(
% 3.70/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).
% 3.70/0.98  
% 3.70/0.98  fof(f83,plain,(
% 3.70/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f58])).
% 3.70/0.98  
% 3.70/0.98  fof(f1,axiom,(
% 3.70/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f51,plain,(
% 3.70/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.70/0.98    inference(nnf_transformation,[],[f1])).
% 3.70/0.98  
% 3.70/0.98  fof(f52,plain,(
% 3.70/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.70/0.98    inference(rectify,[],[f51])).
% 3.70/0.98  
% 3.70/0.98  fof(f53,plain,(
% 3.70/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f54,plain,(
% 3.70/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).
% 3.70/0.99  
% 3.70/0.99  fof(f80,plain,(
% 3.70/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f54])).
% 3.70/0.99  
% 3.70/0.99  fof(f10,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f38,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f10])).
% 3.70/0.99  
% 3.70/0.99  fof(f39,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(flattening,[],[f38])).
% 3.70/0.99  
% 3.70/0.99  fof(f64,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f39])).
% 3.70/0.99  
% 3.70/0.99  fof(f65,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(rectify,[],[f64])).
% 3.70/0.99  
% 3.70/0.99  fof(f66,plain,(
% 3.70/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f67,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f65,f66])).
% 3.70/0.99  
% 3.70/0.99  fof(f98,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f67])).
% 3.70/0.99  
% 3.70/0.99  fof(f17,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f25,plain,(
% 3.70/0.99    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.70/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.70/0.99  
% 3.70/0.99  fof(f112,plain,(
% 3.70/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f25])).
% 3.70/0.99  
% 3.70/0.99  fof(f19,axiom,(
% 3.70/0.99    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f115,plain,(
% 3.70/0.99    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.70/0.99    inference(cnf_transformation,[],[f19])).
% 3.70/0.99  
% 3.70/0.99  fof(f13,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f42,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f13])).
% 3.70/0.99  
% 3.70/0.99  fof(f43,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(flattening,[],[f42])).
% 3.70/0.99  
% 3.70/0.99  fof(f72,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f43])).
% 3.70/0.99  
% 3.70/0.99  fof(f73,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(flattening,[],[f72])).
% 3.70/0.99  
% 3.70/0.99  fof(f74,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(rectify,[],[f73])).
% 3.70/0.99  
% 3.70/0.99  fof(f75,plain,(
% 3.70/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f76,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).
% 3.70/0.99  
% 3.70/0.99  fof(f105,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f76])).
% 3.70/0.99  
% 3.70/0.99  fof(f122,plain,(
% 3.70/0.99    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(equality_resolution,[],[f105])).
% 3.70/0.99  
% 3.70/0.99  fof(f14,axiom,(
% 3.70/0.99    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f44,plain,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f14])).
% 3.70/0.99  
% 3.70/0.99  fof(f109,plain,(
% 3.70/0.99    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f6,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f31,plain,(
% 3.70/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f6])).
% 3.70/0.99  
% 3.70/0.99  fof(f88,plain,(
% 3.70/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f31])).
% 3.70/0.99  
% 3.70/0.99  fof(f5,axiom,(
% 3.70/0.99    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f29,plain,(
% 3.70/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f5])).
% 3.70/0.99  
% 3.70/0.99  fof(f30,plain,(
% 3.70/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 3.70/0.99    inference(flattening,[],[f29])).
% 3.70/0.99  
% 3.70/0.99  fof(f87,plain,(
% 3.70/0.99    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f30])).
% 3.70/0.99  
% 3.70/0.99  fof(f16,axiom,(
% 3.70/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f26,plain,(
% 3.70/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.70/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.70/0.99  
% 3.70/0.99  fof(f46,plain,(
% 3.70/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f26])).
% 3.70/0.99  
% 3.70/0.99  fof(f47,plain,(
% 3.70/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.70/0.99    inference(flattening,[],[f46])).
% 3.70/0.99  
% 3.70/0.99  fof(f111,plain,(
% 3.70/0.99    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f47])).
% 3.70/0.99  
% 3.70/0.99  fof(f18,axiom,(
% 3.70/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f23,plain,(
% 3.70/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.70/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.70/0.99  
% 3.70/0.99  fof(f24,plain,(
% 3.70/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.70/0.99    inference(pure_predicate_removal,[],[f23])).
% 3.70/0.99  
% 3.70/0.99  fof(f114,plain,(
% 3.70/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f24])).
% 3.70/0.99  
% 3.70/0.99  fof(f11,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f40,plain,(
% 3.70/0.99    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f11])).
% 3.70/0.99  
% 3.70/0.99  fof(f100,plain,(
% 3.70/0.99    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f40])).
% 3.70/0.99  
% 3.70/0.99  fof(f20,axiom,(
% 3.70/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f48,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f20])).
% 3.70/0.99  
% 3.70/0.99  fof(f77,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f48])).
% 3.70/0.99  
% 3.70/0.99  fof(f118,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f77])).
% 3.70/0.99  
% 3.70/0.99  fof(f7,axiom,(
% 3.70/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f32,plain,(
% 3.70/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f7])).
% 3.70/0.99  
% 3.70/0.99  fof(f33,plain,(
% 3.70/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.70/0.99    inference(flattening,[],[f32])).
% 3.70/0.99  
% 3.70/0.99  fof(f59,plain,(
% 3.70/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f33])).
% 3.70/0.99  
% 3.70/0.99  fof(f89,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f59])).
% 3.70/0.99  
% 3.70/0.99  fof(f113,plain,(
% 3.70/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f24])).
% 3.70/0.99  
% 3.70/0.99  fof(f8,axiom,(
% 3.70/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f34,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f8])).
% 3.70/0.99  
% 3.70/0.99  fof(f35,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.70/0.99    inference(flattening,[],[f34])).
% 3.70/0.99  
% 3.70/0.99  fof(f91,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f35])).
% 3.70/0.99  
% 3.70/0.99  fof(f15,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f45,plain,(
% 3.70/0.99    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f15])).
% 3.70/0.99  
% 3.70/0.99  fof(f110,plain,(
% 3.70/0.99    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f45])).
% 3.70/0.99  
% 3.70/0.99  fof(f3,axiom,(
% 3.70/0.99    v1_xboole_0(k1_xboole_0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f85,plain,(
% 3.70/0.99    v1_xboole_0(k1_xboole_0)),
% 3.70/0.99    inference(cnf_transformation,[],[f3])).
% 3.70/0.99  
% 3.70/0.99  fof(f9,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f36,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f9])).
% 3.70/0.99  
% 3.70/0.99  fof(f37,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(flattening,[],[f36])).
% 3.70/0.99  
% 3.70/0.99  fof(f60,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f37])).
% 3.70/0.99  
% 3.70/0.99  fof(f61,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(rectify,[],[f60])).
% 3.70/0.99  
% 3.70/0.99  fof(f62,plain,(
% 3.70/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f63,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).
% 3.70/0.99  
% 3.70/0.99  fof(f95,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f63])).
% 3.70/0.99  
% 3.70/0.99  fof(f93,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f63])).
% 3.70/0.99  
% 3.70/0.99  fof(f12,axiom,(
% 3.70/0.99    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f41,plain,(
% 3.70/0.99    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f12])).
% 3.70/0.99  
% 3.70/0.99  fof(f68,plain,(
% 3.70/0.99    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f41])).
% 3.70/0.99  
% 3.70/0.99  fof(f69,plain,(
% 3.70/0.99    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(rectify,[],[f68])).
% 3.70/0.99  
% 3.70/0.99  fof(f70,plain,(
% 3.70/0.99    ! [X0] : (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r1_lattice3(X0,u1_struct_0(X0),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f71,plain,(
% 3.70/0.99    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((r1_lattice3(X0,u1_struct_0(X0),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f69,f70])).
% 3.70/0.99  
% 3.70/0.99  fof(f103,plain,(
% 3.70/0.99    ( ! [X0,X1] : (v1_yellow_0(X0) | ~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f71])).
% 3.70/0.99  
% 3.70/0.99  fof(f94,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f63])).
% 3.70/0.99  
% 3.70/0.99  fof(f121,plain,(
% 3.70/0.99    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6))),
% 3.70/0.99    inference(cnf_transformation,[],[f79])).
% 3.70/0.99  
% 3.70/0.99  fof(f119,plain,(
% 3.70/0.99    ~v1_xboole_0(sK6)),
% 3.70/0.99    inference(cnf_transformation,[],[f79])).
% 3.70/0.99  
% 3.70/0.99  cnf(c_40,negated_conjecture,
% 3.70/0.99      ( r2_hidden(k1_xboole_0,sK6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8112,plain,
% 3.70/0.99      ( r2_hidden(k1_xboole_0,sK6) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6,plain,
% 3.70/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8113,plain,
% 3.70/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.70/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8496,plain,
% 3.70/0.99      ( m1_subset_1(k1_xboole_0,sK6) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8112,c_8113]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3,plain,
% 3.70/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8116,plain,
% 3.70/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.70/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1,negated_conjecture,
% 3.70/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8118,plain,
% 3.70/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8509,plain,
% 3.70/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8116,c_8118]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_17,plain,
% 3.70/0.99      ( r2_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_32,plain,
% 3.70/0.99      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1461,plain,
% 3.70/0.99      ( r2_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 3.70/0.99      | k2_yellow_1(X3) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1462,plain,
% 3.70/0.99      ( r2_lattice3(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | r2_hidden(sK3(k2_yellow_1(X0),X1,X2),X1) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1461]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8092,plain,
% 3.70/0.99      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | r2_hidden(sK3(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_36,plain,
% 3.70/0.99      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8211,plain,
% 3.70/0.99      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | r2_hidden(sK3(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8092,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8660,plain,
% 3.70/0.99      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8211,c_8118]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_27,plain,
% 3.70/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.70/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.70/0.99      | ~ r1_yellow_0(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_29,plain,
% 3.70/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_248,plain,
% 3.70/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ r1_yellow_0(X0,X1)
% 3.70/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.70/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_27,c_29]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_249,plain,
% 3.70/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.70/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.70/0.99      | ~ r1_yellow_0(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_248]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8,plain,
% 3.70/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_7,plain,
% 3.70/0.99      ( ~ v2_struct_0(X0)
% 3.70/0.99      | ~ l1_struct_0(X0)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_464,plain,
% 3.70/0.99      ( ~ l1_orders_2(X0)
% 3.70/0.99      | ~ v2_struct_0(X0)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 3.70/0.99      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_31,plain,
% 3.70/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(X0)
% 3.70/0.99      | ~ v5_orders_2(X0)
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | v2_struct_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_33,plain,
% 3.70/0.99      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_482,plain,
% 3.70/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(X0)
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | v2_struct_0(X0)
% 3.70/0.99      | k2_yellow_1(X1) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_33]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_483,plain,
% 3.70/0.99      ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.70/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_482]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_487,plain,
% 3.70/0.99      ( ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_483,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_488,plain,
% 3.70/0.99      ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_487]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_730,plain,
% 3.70/0.99      ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | ~ l1_orders_2(X1)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(X1))
% 3.70/0.99      | k2_yellow_1(X0) != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_464,c_488]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_731,plain,
% 3.70/0.99      ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_730]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_735,plain,
% 3.70/0.99      ( ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_731,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_736,plain,
% 3.70/0.99      ( r1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_735]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_974,plain,
% 3.70/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.70/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X3))
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X3)))
% 3.70/0.99      | k2_yellow_1(X3) != X0
% 3.70/0.99      | k1_xboole_0 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_249,c_736]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_975,plain,
% 3.70/0.99      ( ~ r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_974]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_979,plain,
% 3.70/0.99      ( ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1)
% 3.70/0.99      | ~ r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_975,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_980,plain,
% 3.70/0.99      ( ~ r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_979]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8106,plain,
% 3.70/0.99      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),k1_xboole_0),X1) = iProver_top
% 3.70/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_20,plain,
% 3.70/0.99      ( ~ l1_orders_2(X0)
% 3.70/0.99      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1419,plain,
% 3.70/0.99      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 3.70/0.99      | k2_yellow_1(X1) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1420,plain,
% 3.70/0.99      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1419]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8282,plain,
% 3.70/0.99      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) = iProver_top
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8106,c_36,c_1420]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_37,plain,
% 3.70/0.99      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ r1_tarski(X1,X2)
% 3.70/0.99      | v1_xboole_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10,plain,
% 3.70/0.99      ( r1_orders_2(X0,X1,X2)
% 3.70/0.99      | ~ r3_orders_2(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.99      | ~ v3_orders_2(X0)
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | v2_struct_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_34,plain,
% 3.70/0.99      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_540,plain,
% 3.70/0.99      ( r1_orders_2(X0,X1,X2)
% 3.70/0.99      | ~ r3_orders_2(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | v2_struct_0(X0)
% 3.70/0.99      | k2_yellow_1(X3) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_34]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_541,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.70/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_540]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_545,plain,
% 3.70/0.99      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_541,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_546,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_545]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_703,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ l1_orders_2(X3)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(X3))
% 3.70/0.99      | k2_yellow_1(X0) != X3 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_464,c_546]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_704,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_703]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_708,plain,
% 3.70/0.99      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_704,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_709,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_708]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1165,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ r1_tarski(X1,X2)
% 3.70/0.99      | v1_xboole_0(X0)
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(resolution,[status(thm)],[c_37,c_709]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8100,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8293,plain,
% 3.70/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8100,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_11,plain,
% 3.70/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.70/0.99      | ~ r1_orders_2(X0,X2,X1)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.99      | ~ v5_orders_2(X0)
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | X1 = X2 ),
% 3.70/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_503,plain,
% 3.70/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.70/0.99      | ~ r1_orders_2(X0,X2,X1)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0)
% 3.70/0.99      | X1 = X2
% 3.70/0.99      | k2_yellow_1(X3) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_504,plain,
% 3.70/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.70/0.99      | X2 = X1 ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_503]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_508,plain,
% 3.70/0.99      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
% 3.70/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | X2 = X1 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_504,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_509,plain,
% 3.70/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | X2 = X1 ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_508]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8107,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2))) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8249,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,X2) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,X2) != iProver_top ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_8107,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8903,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,X2) != iProver_top
% 3.70/0.99      | m1_subset_1(X0,X2) != iProver_top
% 3.70/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.70/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8293,c_8249]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9367,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) != iProver_top
% 3.70/0.99      | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8282,c_8903]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_30,plain,
% 3.70/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1362,plain,
% 3.70/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.70/0.99      | k2_yellow_1(X1) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1363,plain,
% 3.70/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1362]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8099,plain,
% 3.70/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8134,plain,
% 3.70/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8099,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_13972,plain,
% 3.70/0.99      ( m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
% 3.70/0.99      | k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_9367,c_8134]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_13973,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_13972]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_13983,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8660,c_13973]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5,plain,
% 3.70/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_142,plain,
% 3.70/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14178,plain,
% 3.70/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | k3_yellow_0(k2_yellow_1(X0)) = X1 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_13983,c_142]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14179,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | r1_tarski(X1,k3_yellow_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_14178]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14187,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8509,c_14179]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_12,plain,
% 3.70/0.99      ( r1_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1542,plain,
% 3.70/0.99      ( r1_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | k2_yellow_1(X3) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1543,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1542]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8087,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8235,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8087,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8905,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) != iProver_top
% 3.70/0.99      | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8293,c_8235]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14,plain,
% 3.70/0.99      ( r1_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1512,plain,
% 3.70/0.99      ( r1_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.70/0.99      | k2_yellow_1(X3) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1513,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1512]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8089,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8218,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8089,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9493,plain,
% 3.70/0.99      ( m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_8905,c_8218]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9494,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_9493]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9501,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | v1_xboole_0(X2) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8509,c_9494]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_21,plain,
% 3.70/0.99      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.99      | v1_yellow_0(X0)
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1404,plain,
% 3.70/0.99      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.99      | v1_yellow_0(X0)
% 3.70/0.99      | k2_yellow_1(X2) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1405,plain,
% 3.70/0.99      ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
% 3.70/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1404]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8095,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8197,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X0,X1) != iProver_top
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8095,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9529,plain,
% 3.70/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_9501,c_8197]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_13,plain,
% 3.70/0.99      ( r1_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.70/0.99      | ~ l1_orders_2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1527,plain,
% 3.70/0.99      ( r1_lattice3(X0,X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.70/0.99      | k2_yellow_1(X3) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1528,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.70/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.70/0.99      | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_1527]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8088,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.70/0.99      | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1528]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8204,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_8088,c_36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8620,plain,
% 3.70/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.70/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8204,c_8118]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8763,plain,
% 3.70/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
% 3.70/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8620,c_8197]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9953,plain,
% 3.70/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
% 3.70/0.99      | m1_subset_1(X0,X1) != iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_9529,c_8763]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9954,plain,
% 3.70/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.70/0.99      | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
% 3.70/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_9953]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14243,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 3.70/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.70/0.99      | v1_xboole_0(X1) != iProver_top
% 3.70/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_14187,c_9954]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14251,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(sK6)) = k1_xboole_0
% 3.70/0.99      | v1_xboole_0(sK6) = iProver_top
% 3.70/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8496,c_14243]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2729,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10911,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(sK6)) != X0
% 3.70/0.99      | k1_xboole_0 != X0
% 3.70/0.99      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK6)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2729]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10912,plain,
% 3.70/0.99      ( k3_yellow_0(k2_yellow_1(sK6)) != k1_xboole_0
% 3.70/0.99      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK6))
% 3.70/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_10911]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2728,plain,( X0 = X0 ),theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2763,plain,
% 3.70/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2728]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_39,negated_conjecture,
% 3.70/0.99      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK6)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_41,negated_conjecture,
% 3.70/0.99      ( ~ v1_xboole_0(sK6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_42,plain,
% 3.70/0.99      ( v1_xboole_0(sK6) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(contradiction,plain,
% 3.70/0.99      ( $false ),
% 3.70/0.99      inference(minisat,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_14251,c_10912,c_2763,c_142,c_39,c_42]) ).
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  ------                               Statistics
% 3.70/0.99  
% 3.70/0.99  ------ Selected
% 3.70/0.99  
% 3.70/0.99  total_time:                             0.344
% 3.70/0.99  
%------------------------------------------------------------------------------

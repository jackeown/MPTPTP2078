%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:56 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 373 expanded)
%              Number of clauses        :   81 ( 137 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   23
%              Number of atoms          :  516 (1735 expanded)
%              Number of equality atoms :   78 ( 123 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
       => v3_lattice3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
         => v3_lattice3(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,
    ( ? [X0] :
        ( ~ v3_lattice3(X0)
        & ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v3_lattice3(sK4)
      & ! [X1] :
          ( r1_yellow_0(sK4,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ v3_lattice3(sK4)
    & ! [X1] :
        ( r1_yellow_0(sK4,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
    & l1_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f32])).

fof(f54,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK2(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK2(X0,X4))
        & m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X2))
        & r2_lattice3(X0,X1,sK1(X0,X2))
        & m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK0(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK0(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK1(X0,X2))
                & r2_lattice3(X0,sK0(X0),sK1(X0,X2))
                & m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK0(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK2(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK2(X0,X4))
              & m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f39,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | r2_lattice3(X0,sK0(X0),sK1(X0,X2))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ~ v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X1] :
      ( r1_yellow_0(sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | ~ r1_orders_2(X0,X2,sK1(X0,X2))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X2,X0] :
      ( v3_lattice3(X0)
      | m1_subset_1(sK1(X0,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK0(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_134,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_135,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_445,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_21])).

cnf(c_446,plain,
    ( r2_lattice3(sK4,X0,k1_yellow_0(sK4,X0))
    | ~ r1_yellow_0(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_888,plain,
    ( r2_lattice3(sK4,X0_47,k1_yellow_0(sK4,X0_47))
    | ~ r1_yellow_0(sK4,X0_47) ),
    inference(subtyping,[status(esa)],[c_446])).

cnf(c_1275,plain,
    ( r2_lattice3(sK4,X0_47,k1_yellow_0(sK4,X0_47)) = iProver_top
    | r1_yellow_0(sK4,X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_556,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | r2_lattice3(X0,sK0(X0),sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v3_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_557,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | r2_lattice3(sK4,sK0(sK4),sK1(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v3_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_19,negated_conjecture,
    ( ~ v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_lattice3(sK4,sK0(sK4),sK1(sK4,X0))
    | ~ r2_lattice3(sK4,sK0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_19])).

cnf(c_562,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | r2_lattice3(sK4,sK0(sK4),sK1(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_561])).

cnf(c_882,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0_47)
    | r2_lattice3(sK4,sK0(sK4),sK1(sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_562])).

cnf(c_1281,plain,
    ( r2_lattice3(sK4,sK0(sK4),X0_47) != iProver_top
    | r2_lattice3(sK4,sK0(sK4),sK1(sK4,X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_12])).

cnf(c_142,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_427,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_142,c_21])).

cnf(c_428,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,k1_yellow_0(sK4,X0),X1)
    | ~ r1_yellow_0(sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_889,plain,
    ( ~ r2_lattice3(sK4,X0_47,X1_47)
    | r1_orders_2(sK4,k1_yellow_0(sK4,X0_47),X1_47)
    | ~ r1_yellow_0(sK4,X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_1274,plain,
    ( r2_lattice3(sK4,X0_47,X1_47) != iProver_top
    | r1_orders_2(sK4,k1_yellow_0(sK4,X0_47),X1_47) = iProver_top
    | r1_yellow_0(sK4,X0_47) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_17,plain,
    ( r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_289,plain,
    ( r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_290,plain,
    ( r1_yellow_0(sK4,X0)
    | ~ r1_yellow_0(sK4,k3_xboole_0(X0,u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_745,plain,
    ( r1_yellow_0(sK4,X0)
    | ~ r1_yellow_0(sK4,k3_xboole_0(X0,u1_struct_0(sK4))) ),
    inference(prop_impl,[status(thm)],[c_21,c_290])).

cnf(c_890,plain,
    ( r1_yellow_0(sK4,X0_47)
    | ~ r1_yellow_0(sK4,k3_xboole_0(X0_47,u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_745])).

cnf(c_922,plain,
    ( r1_yellow_0(sK4,X0_47) = iProver_top
    | r1_yellow_0(sK4,k3_xboole_0(X0_47,u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_925,plain,
    ( r2_lattice3(sK4,X0_47,X1_47) != iProver_top
    | r1_orders_2(sK4,k1_yellow_0(sK4,X0_47),X1_47) = iProver_top
    | r1_yellow_0(sK4,X0_47) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_13,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_260,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k3_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_261,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_892,plain,
    ( m1_subset_1(k3_xboole_0(X0_47,X1_47),k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_1411,plain,
    ( m1_subset_1(k3_xboole_0(u1_struct_0(sK4),X0_47),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_1413,plain,
    ( m1_subset_1(k3_xboole_0(u1_struct_0(sK4),X0_47),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_20,negated_conjecture,
    ( r1_yellow_0(sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_893,negated_conjecture,
    ( r1_yellow_0(sK4,X0_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1412,plain,
    ( r1_yellow_0(sK4,k3_xboole_0(u1_struct_0(sK4),X0_47))
    | ~ m1_subset_1(k3_xboole_0(u1_struct_0(sK4),X0_47),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_1417,plain,
    ( r1_yellow_0(sK4,k3_xboole_0(u1_struct_0(sK4),X0_47)) = iProver_top
    | m1_subset_1(k3_xboole_0(u1_struct_0(sK4),X0_47),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_902,plain,
    ( ~ r1_yellow_0(X0_46,X0_47)
    | r1_yellow_0(X0_46,X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1476,plain,
    ( r1_yellow_0(sK4,X0_47)
    | ~ r1_yellow_0(sK4,k3_xboole_0(u1_struct_0(sK4),X1_47))
    | X0_47 != k3_xboole_0(u1_struct_0(sK4),X1_47) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_1577,plain,
    ( r1_yellow_0(sK4,k3_xboole_0(X0_47,u1_struct_0(sK4)))
    | ~ r1_yellow_0(sK4,k3_xboole_0(u1_struct_0(sK4),X0_47))
    | k3_xboole_0(X0_47,u1_struct_0(sK4)) != k3_xboole_0(u1_struct_0(sK4),X0_47) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_1579,plain,
    ( k3_xboole_0(X0_47,u1_struct_0(sK4)) != k3_xboole_0(u1_struct_0(sK4),X0_47)
    | r1_yellow_0(sK4,k3_xboole_0(X0_47,u1_struct_0(sK4))) = iProver_top
    | r1_yellow_0(sK4,k3_xboole_0(u1_struct_0(sK4),X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_894,plain,
    ( k3_xboole_0(X0_47,X1_47) = k3_xboole_0(X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1578,plain,
    ( k3_xboole_0(X0_47,u1_struct_0(sK4)) = k3_xboole_0(u1_struct_0(sK4),X0_47) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_1614,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,X0_47),X1_47) = iProver_top
    | r2_lattice3(sK4,X0_47,X1_47) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1274,c_922,c_925,c_1413,c_1417,c_1579,c_1578])).

cnf(c_1615,plain,
    ( r2_lattice3(sK4,X0_47,X1_47) != iProver_top
    | r1_orders_2(sK4,k1_yellow_0(sK4,X0_47),X1_47) = iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1614])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ r1_orders_2(X0,X1,sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_577,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ r1_orders_2(X0,X1,sK1(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v3_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_578,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | ~ r1_orders_2(sK4,X0,sK1(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v3_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,X0,sK1(sK4,X0))
    | ~ r2_lattice3(sK4,sK0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_19])).

cnf(c_583,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | ~ r1_orders_2(sK4,X0,sK1(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_881,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0_47)
    | ~ r1_orders_2(sK4,X0_47,sK1(sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_1282,plain,
    ( r2_lattice3(sK4,sK0(sK4),X0_47) != iProver_top
    | r1_orders_2(sK4,X0_47,sK1(sK4,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_1623,plain,
    ( r2_lattice3(sK4,X0_47,sK1(sK4,k1_yellow_0(sK4,X0_47))) != iProver_top
    | r2_lattice3(sK4,sK0(sK4),k1_yellow_0(sK4,X0_47)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X0_47),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,k1_yellow_0(sK4,X0_47)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1615,c_1282])).

cnf(c_457,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_458,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_887,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0_47),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_931,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0_47),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_535,plain,
    ( ~ r2_lattice3(X0,sK0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | v3_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_536,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v3_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_lattice3(sK4,sK0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_19])).

cnf(c_541,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_883,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_47),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_541])).

cnf(c_1396,plain,
    ( ~ r2_lattice3(sK4,sK0(sK4),k1_yellow_0(sK4,X0_47))
    | ~ m1_subset_1(k1_yellow_0(sK4,X0_47),u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,k1_yellow_0(sK4,X0_47)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_1397,plain,
    ( r2_lattice3(sK4,sK0(sK4),k1_yellow_0(sK4,X0_47)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X0_47),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,k1_yellow_0(sK4,X0_47)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_1900,plain,
    ( r2_lattice3(sK4,X0_47,sK1(sK4,k1_yellow_0(sK4,X0_47))) != iProver_top
    | r2_lattice3(sK4,sK0(sK4),k1_yellow_0(sK4,X0_47)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1623,c_931,c_1397])).

cnf(c_1908,plain,
    ( r2_lattice3(sK4,sK0(sK4),k1_yellow_0(sK4,sK0(sK4))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,sK0(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1900])).

cnf(c_1815,plain,
    ( m1_subset_1(k1_yellow_0(sK4,sK0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_1816,plain,
    ( m1_subset_1(k1_yellow_0(sK4,sK0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_1911,plain,
    ( r2_lattice3(sK4,sK0(sK4),k1_yellow_0(sK4,sK0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1908,c_1816])).

cnf(c_1916,plain,
    ( r1_yellow_0(sK4,sK0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_1911])).

cnf(c_1273,plain,
    ( r1_yellow_0(sK4,X0_47) = iProver_top
    | r1_yellow_0(sK4,k3_xboole_0(X0_47,u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_1749,plain,
    ( r1_yellow_0(sK4,X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1273,c_922,c_1413,c_1417,c_1579,c_1578])).

cnf(c_1951,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1916,c_1749])).


%------------------------------------------------------------------------------

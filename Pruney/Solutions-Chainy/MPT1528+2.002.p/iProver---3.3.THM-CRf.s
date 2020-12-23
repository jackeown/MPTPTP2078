%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:24 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  228 (8188 expanded)
%              Number of clauses        :  176 (2804 expanded)
%              Number of leaves         :   19 (1948 expanded)
%              Depth                    :   26
%              Number of atoms          :  783 (34602 expanded)
%              Number of equality atoms :  348 (7422 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,k1_xboole_0,sK4)
          | ~ r2_lattice3(X0,k1_xboole_0,sK4) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK3,k1_xboole_0,X1)
            | ~ r2_lattice3(sK3,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_lattice3(sK3,k1_xboole_0,sK4)
      | ~ r2_lattice3(sK3,k1_xboole_0,sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,
    ( ~ r1_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r2_lattice3(sK3,k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1435,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2162,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_2578,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_8691,plain,
    ( sK1(sK3,k1_xboole_0,sK4) != sK4
    | sK4 = sK1(sK3,k1_xboole_0,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_7623,plain,
    ( X0 != sK1(sK3,k1_xboole_0,sK4)
    | sK4 = X0
    | sK4 != sK1(sK3,k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_7625,plain,
    ( sK4 != sK1(sK3,k1_xboole_0,sK4)
    | sK4 = sK3
    | sK3 != sK1(sK3,k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_7623])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1789,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_326,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_327,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_1782,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1792,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1793,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2600,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1793])).

cnf(c_2766,plain,
    ( r1_lattice3(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_2600])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1794,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2964,plain,
    ( sK1(sK3,k1_xboole_0,X0) = X1
    | r1_lattice3(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_1794])).

cnf(c_4446,plain,
    ( sK1(sK3,k1_xboole_0,sK4) = X0
    | r1_lattice3(sK3,k1_xboole_0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_2964])).

cnf(c_12,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_290,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_291,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1784,plain,
    ( r1_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK3,X1,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_2176,plain,
    ( r1_lattice3(sK3,X0,sK4) != iProver_top
    | r1_orders_2(sK3,sK4,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_1784])).

cnf(c_2181,plain,
    ( r1_lattice3(sK3,X0,sK4) != iProver_top
    | r1_orders_2(sK3,sK4,sK4) = iProver_top
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_2176])).

cnf(c_4537,plain,
    ( sK1(sK3,k1_xboole_0,sK4) = X0
    | r1_orders_2(sK3,sK4,sK4) = iProver_top
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4446,c_2181])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_260,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_261,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_1786,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_2765,plain,
    ( r2_lattice3(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_2600])).

cnf(c_2914,plain,
    ( sK2(sK3,k1_xboole_0,X0) = X1
    | r2_lattice3(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2765,c_1794])).

cnf(c_3976,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = X0
    | r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_2914])).

cnf(c_17,negated_conjecture,
    ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r1_lattice3(sK3,k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1790,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4) != iProver_top
    | r1_lattice3(sK3,k1_xboole_0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3993,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = X0
    | r1_lattice3(sK3,k1_xboole_0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_1790])).

cnf(c_4536,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = X0
    | sK1(sK3,k1_xboole_0,sK4) = X1 ),
    inference(superposition,[status(thm)],[c_4446,c_3993])).

cnf(c_4662,plain,
    ( sK2(sK3,k1_xboole_0,sK4) != X0
    | sK1(sK3,k1_xboole_0,sK4) = X0 ),
    inference(equality_factoring,[status(thm)],[c_4536])).

cnf(c_5004,plain,
    ( sK1(sK3,k1_xboole_0,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4537,c_3993,c_4446,c_4662])).

cnf(c_15,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_245,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_246,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_1787,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_5012,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5004,c_1787])).

cnf(c_2216,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2217,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2216])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1958,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_2794,plain,
    ( m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_2795,plain,
    ( m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_5013,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5004,c_1786])).

cnf(c_5423,plain,
    ( r1_lattice3(sK3,k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5013,c_1790])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1870,plain,
    ( r1_lattice3(sK3,X0,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1931,plain,
    ( r1_lattice3(sK3,k1_xboole_0,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_1932,plain,
    ( r1_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1931])).

cnf(c_5714,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5423,c_21,c_1932])).

cnf(c_6126,plain,
    ( m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5012,c_21,c_1932,c_2217,c_2795,c_5423])).

cnf(c_6130,plain,
    ( r1_lattice3(sK3,X0,sK4) != iProver_top
    | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4)) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6126,c_2176])).

cnf(c_56,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_61,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_64,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_341,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_342,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_498,plain,
    ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r1_orders_2(sK3,X0,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | sK4 != X0
    | sK3 != sK3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_342])).

cnf(c_499,plain,
    ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_500,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4) != iProver_top
    | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1440,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1449,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_1834,plain,
    ( r2_lattice3(sK3,X0,sK4)
    | m1_subset_1(sK2(sK3,X0,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1914,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4)
    | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_1915,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_1907,plain,
    ( ~ r1_lattice3(sK3,X0,sK4)
    | r1_orders_2(sK3,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1985,plain,
    ( ~ r1_lattice3(sK3,X0,sK4)
    | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4))
    | ~ m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_2041,plain,
    ( r1_lattice3(sK3,X0,sK4) != iProver_top
    | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4)) = iProver_top
    | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_13,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_275,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_276,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK2(sK3,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_1863,plain,
    ( r2_lattice3(sK3,X0,sK4)
    | ~ r1_orders_2(sK3,sK2(sK3,X0,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_2066,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4)
    | ~ r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_2068,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
    | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(c_1856,plain,
    ( r2_lattice3(sK3,X0,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_2065,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_2070,plain,
    ( r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2065])).

cnf(c_1436,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2152,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_2153,plain,
    ( X0 != X1
    | sK4 != X2
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_2155,plain,
    ( sK4 != sK3
    | sK3 != sK3
    | r2_hidden(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2153])).

cnf(c_2303,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK4))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2304,plain,
    ( X0 = sK4
    | r2_hidden(X0,k1_tarski(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_2306,plain,
    ( sK3 = sK4
    | r2_hidden(sK3,k1_tarski(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_1437,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1844,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,u1_struct_0(sK3))
    | X2 != X0
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_1979,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X1,u1_struct_0(sK3))
    | X1 != X0
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_2327,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
    | X0 != sK1(sK3,k1_xboole_0,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_2329,plain,
    ( X0 != sK1(sK3,k1_xboole_0,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_2331,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != sK1(sK3,k1_xboole_0,sK4)
    | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2329])).

cnf(c_2360,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2163,plain,
    ( ~ r2_hidden(sK4,k1_tarski(X0))
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2468,plain,
    ( ~ r2_hidden(sK4,k1_tarski(sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_2510,plain,
    ( X0 != X1
    | X0 = sK1(sK3,k1_xboole_0,sK4)
    | sK1(sK3,k1_xboole_0,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_2511,plain,
    ( sK1(sK3,k1_xboole_0,sK4) != sK3
    | sK3 = sK1(sK3,k1_xboole_0,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2510])).

cnf(c_2579,plain,
    ( sK4 != sK4
    | sK4 = sK3
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_2374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0)
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2736,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0)
    | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_2737,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2736])).

cnf(c_2739,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),sK3) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2737])).

cnf(c_3586,plain,
    ( X0 != X1
    | X0 = sK2(sK3,k1_xboole_0,sK4)
    | sK2(sK3,k1_xboole_0,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_3587,plain,
    ( sK2(sK3,k1_xboole_0,sK4) != sK3
    | sK3 = sK2(sK3,k1_xboole_0,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_3599,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),X2)
    | X1 != X2
    | X0 != sK1(sK3,k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_3600,plain,
    ( X0 != X1
    | X2 != sK1(sK3,k1_xboole_0,sK4)
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3599])).

cnf(c_3602,plain,
    ( sK3 != sK1(sK3,k1_xboole_0,sK4)
    | sK3 != sK3
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),sK3) != iProver_top
    | r2_hidden(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3600])).

cnf(c_2075,plain,
    ( ~ r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4))
    | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_3767,plain,
    ( ~ r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4))
    | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4)
    | ~ m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_3768,plain,
    ( r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4)) != iProver_top
    | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4) = iProver_top
    | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3767])).

cnf(c_3770,plain,
    ( r1_lattice3(sK3,sK3,sK2(sK3,k1_xboole_0,sK4)) != iProver_top
    | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4) = iProver_top
    | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3768])).

cnf(c_2490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tarski(sK4)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4162,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4)))
    | r2_hidden(X0,k1_tarski(sK4))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2490])).

cnf(c_4163,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) != iProver_top
    | r2_hidden(X0,k1_tarski(sK4)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4162])).

cnf(c_4165,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) != iProver_top
    | r2_hidden(sK3,k1_tarski(sK4)) = iProver_top
    | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4163])).

cnf(c_4660,plain,
    ( sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4)
    | sK1(sK3,k1_xboole_0,sK4) = X0 ),
    inference(equality_factoring,[status(thm)],[c_4536])).

cnf(c_4904,plain,
    ( sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4)
    | sK1(sK3,k1_xboole_0,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_4660])).

cnf(c_4661,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = sK1(sK3,k1_xboole_0,sK4)
    | sK1(sK3,k1_xboole_0,sK4) != X0 ),
    inference(equality_factoring,[status(thm)],[c_4536])).

cnf(c_4663,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = X0
    | sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4) ),
    inference(equality_factoring,[status(thm)],[c_4536])).

cnf(c_4907,plain,
    ( sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4)
    | sK2(sK3,k1_xboole_0,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_4663])).

cnf(c_5606,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5607,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5606])).

cnf(c_5718,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5714,c_2600])).

cnf(c_7,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_374,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_375,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1779,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_5082,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5004,c_1779])).

cnf(c_1980,plain,
    ( X0 != X1
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1979])).

cnf(c_5069,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_5004,c_5004])).

cnf(c_5301,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,X1) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5082,c_61,c_64,c_1449,c_1980,c_5069])).

cnf(c_5302,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5301])).

cnf(c_5814,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5718,c_5302])).

cnf(c_5822,plain,
    ( r1_orders_2(sK3,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5814])).

cnf(c_1795,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4602,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = X0
    | r2_hidden(X1,sK1(sK3,k1_xboole_0,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4536,c_1795])).

cnf(c_5627,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4602,c_3993,c_4446,c_4661,c_4662,c_4663])).

cnf(c_1781,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,X1,sK1(sK3,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_5650,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,X1,sK2(sK3,k1_xboole_0,sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5627,c_1781])).

cnf(c_5825,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5627,c_5650])).

cnf(c_5827,plain,
    ( r1_lattice3(sK3,sK3,sK3) = iProver_top
    | r1_orders_2(sK3,sK3,sK3) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5825])).

cnf(c_1441,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_5901,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(sK3,X3,sK2(sK3,k1_xboole_0,sK4))
    | X3 != X1
    | sK2(sK3,k1_xboole_0,sK4) != X2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_5902,plain,
    ( X0 != X1
    | sK2(sK3,k1_xboole_0,sK4) != X2
    | sK3 != X3
    | r1_lattice3(X3,X1,X2) != iProver_top
    | r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5901])).

cnf(c_5904,plain,
    ( sK2(sK3,k1_xboole_0,sK4) != sK3
    | sK3 != sK3
    | r1_lattice3(sK3,sK3,sK2(sK3,k1_xboole_0,sK4)) = iProver_top
    | r1_lattice3(sK3,sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5902])).

cnf(c_1434,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5989,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_3520,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0)
    | X0 != sK2(sK3,k1_xboole_0,sK4)
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_6251,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0)
    | X0 != sK2(sK3,k1_xboole_0,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3520])).

cnf(c_6252,plain,
    ( X0 != sK2(sK3,k1_xboole_0,sK4)
    | k1_xboole_0 != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6251])).

cnf(c_6254,plain,
    ( sK3 != sK2(sK3,k1_xboole_0,sK4)
    | k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6252])).

cnf(c_6296,plain,
    ( r1_lattice3(sK3,X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6130,c_21,c_56,c_58,c_61,c_64,c_500,c_1449,c_1915,c_1932,c_2041,c_2068,c_2070,c_2155,c_2217,c_2306,c_2331,c_2360,c_2468,c_2511,c_2579,c_2737,c_2739,c_2795,c_3587,c_3602,c_3770,c_3993,c_4165,c_4446,c_4904,c_4661,c_4662,c_4907,c_5423,c_5607,c_5822,c_5827,c_5904,c_5989,c_6254])).

cnf(c_6299,plain,
    ( r1_lattice3(sK3,sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6296])).

cnf(c_3617,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4))
    | sK1(sK3,k1_xboole_0,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_3620,plain,
    ( sK1(sK3,k1_xboole_0,sK4) = sK4
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3617])).

cnf(c_3616,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4)))
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4))
    | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_3618,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) != iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4)) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3616])).

cnf(c_3333,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(sK3,X3,sK4)
    | X3 != X1
    | sK4 != X2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_3334,plain,
    ( X0 != X1
    | sK4 != X2
    | sK3 != X3
    | r1_lattice3(X3,X1,X2) != iProver_top
    | r1_lattice3(sK3,X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3333])).

cnf(c_3336,plain,
    ( sK4 != sK3
    | sK3 != sK3
    | r1_lattice3(sK3,sK3,sK4) = iProver_top
    | r1_lattice3(sK3,sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3334])).

cnf(c_8699,plain,
    ( sK1(sK3,k1_xboole_0,sK4) = sK3 ),
    inference(grounding,[status(thm)],[c_5004:[bind(X0,$fot(sK3))]])).

cnf(c_8700,plain,
    ( sK2(sK3,k1_xboole_0,sK4) = sK1(sK3,k1_xboole_0,sK4)
    | sK1(sK3,k1_xboole_0,sK4) != sK3 ),
    inference(grounding,[status(thm)],[c_4661:[bind(X0,$fot(sK3))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8691,c_7625,c_6299,c_5827,c_5822,c_5714,c_5607,c_8699,c_8700,c_4904,c_3620,c_3618,c_3336,c_2795,c_2511,c_2468,c_2360,c_2331,c_2217,c_1449,c_64,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.65/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.01  
% 3.65/1.01  ------  iProver source info
% 3.65/1.01  
% 3.65/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.01  git: non_committed_changes: false
% 3.65/1.01  git: last_make_outside_of_git: false
% 3.65/1.01  
% 3.65/1.01  ------ 
% 3.65/1.01  
% 3.65/1.01  ------ Input Options
% 3.65/1.01  
% 3.65/1.01  --out_options                           all
% 3.65/1.01  --tptp_safe_out                         true
% 3.65/1.01  --problem_path                          ""
% 3.65/1.01  --include_path                          ""
% 3.65/1.01  --clausifier                            res/vclausify_rel
% 3.65/1.01  --clausifier_options                    ""
% 3.65/1.01  --stdin                                 false
% 3.65/1.01  --stats_out                             all
% 3.65/1.01  
% 3.65/1.01  ------ General Options
% 3.65/1.01  
% 3.65/1.01  --fof                                   false
% 3.65/1.01  --time_out_real                         305.
% 3.65/1.01  --time_out_virtual                      -1.
% 3.65/1.01  --symbol_type_check                     false
% 3.65/1.01  --clausify_out                          false
% 3.65/1.01  --sig_cnt_out                           false
% 3.65/1.01  --trig_cnt_out                          false
% 3.65/1.01  --trig_cnt_out_tolerance                1.
% 3.65/1.01  --trig_cnt_out_sk_spl                   false
% 3.65/1.01  --abstr_cl_out                          false
% 3.65/1.01  
% 3.65/1.01  ------ Global Options
% 3.65/1.01  
% 3.65/1.01  --schedule                              default
% 3.65/1.01  --add_important_lit                     false
% 3.65/1.01  --prop_solver_per_cl                    1000
% 3.65/1.01  --min_unsat_core                        false
% 3.65/1.01  --soft_assumptions                      false
% 3.65/1.01  --soft_lemma_size                       3
% 3.65/1.01  --prop_impl_unit_size                   0
% 3.65/1.01  --prop_impl_unit                        []
% 3.65/1.01  --share_sel_clauses                     true
% 3.65/1.01  --reset_solvers                         false
% 3.65/1.01  --bc_imp_inh                            [conj_cone]
% 3.65/1.01  --conj_cone_tolerance                   3.
% 3.65/1.01  --extra_neg_conj                        none
% 3.65/1.01  --large_theory_mode                     true
% 3.65/1.01  --prolific_symb_bound                   200
% 3.65/1.01  --lt_threshold                          2000
% 3.65/1.01  --clause_weak_htbl                      true
% 3.65/1.01  --gc_record_bc_elim                     false
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing Options
% 3.65/1.01  
% 3.65/1.01  --preprocessing_flag                    true
% 3.65/1.01  --time_out_prep_mult                    0.1
% 3.65/1.01  --splitting_mode                        input
% 3.65/1.01  --splitting_grd                         true
% 3.65/1.01  --splitting_cvd                         false
% 3.65/1.01  --splitting_cvd_svl                     false
% 3.65/1.01  --splitting_nvd                         32
% 3.65/1.01  --sub_typing                            true
% 3.65/1.01  --prep_gs_sim                           true
% 3.65/1.01  --prep_unflatten                        true
% 3.65/1.01  --prep_res_sim                          true
% 3.65/1.01  --prep_upred                            true
% 3.65/1.01  --prep_sem_filter                       exhaustive
% 3.65/1.01  --prep_sem_filter_out                   false
% 3.65/1.01  --pred_elim                             true
% 3.65/1.01  --res_sim_input                         true
% 3.65/1.01  --eq_ax_congr_red                       true
% 3.65/1.01  --pure_diseq_elim                       true
% 3.65/1.01  --brand_transform                       false
% 3.65/1.01  --non_eq_to_eq                          false
% 3.65/1.01  --prep_def_merge                        true
% 3.65/1.01  --prep_def_merge_prop_impl              false
% 3.65/1.01  --prep_def_merge_mbd                    true
% 3.65/1.01  --prep_def_merge_tr_red                 false
% 3.65/1.01  --prep_def_merge_tr_cl                  false
% 3.65/1.01  --smt_preprocessing                     true
% 3.65/1.01  --smt_ac_axioms                         fast
% 3.65/1.01  --preprocessed_out                      false
% 3.65/1.01  --preprocessed_stats                    false
% 3.65/1.01  
% 3.65/1.01  ------ Abstraction refinement Options
% 3.65/1.01  
% 3.65/1.01  --abstr_ref                             []
% 3.65/1.01  --abstr_ref_prep                        false
% 3.65/1.01  --abstr_ref_until_sat                   false
% 3.65/1.01  --abstr_ref_sig_restrict                funpre
% 3.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.01  --abstr_ref_under                       []
% 3.65/1.01  
% 3.65/1.01  ------ SAT Options
% 3.65/1.01  
% 3.65/1.01  --sat_mode                              false
% 3.65/1.01  --sat_fm_restart_options                ""
% 3.65/1.01  --sat_gr_def                            false
% 3.65/1.01  --sat_epr_types                         true
% 3.65/1.01  --sat_non_cyclic_types                  false
% 3.65/1.01  --sat_finite_models                     false
% 3.65/1.01  --sat_fm_lemmas                         false
% 3.65/1.01  --sat_fm_prep                           false
% 3.65/1.01  --sat_fm_uc_incr                        true
% 3.65/1.01  --sat_out_model                         small
% 3.65/1.01  --sat_out_clauses                       false
% 3.65/1.01  
% 3.65/1.01  ------ QBF Options
% 3.65/1.01  
% 3.65/1.01  --qbf_mode                              false
% 3.65/1.01  --qbf_elim_univ                         false
% 3.65/1.01  --qbf_dom_inst                          none
% 3.65/1.01  --qbf_dom_pre_inst                      false
% 3.65/1.01  --qbf_sk_in                             false
% 3.65/1.01  --qbf_pred_elim                         true
% 3.65/1.01  --qbf_split                             512
% 3.65/1.01  
% 3.65/1.01  ------ BMC1 Options
% 3.65/1.01  
% 3.65/1.01  --bmc1_incremental                      false
% 3.65/1.01  --bmc1_axioms                           reachable_all
% 3.65/1.01  --bmc1_min_bound                        0
% 3.65/1.01  --bmc1_max_bound                        -1
% 3.65/1.01  --bmc1_max_bound_default                -1
% 3.65/1.01  --bmc1_symbol_reachability              true
% 3.65/1.01  --bmc1_property_lemmas                  false
% 3.65/1.01  --bmc1_k_induction                      false
% 3.65/1.01  --bmc1_non_equiv_states                 false
% 3.65/1.01  --bmc1_deadlock                         false
% 3.65/1.01  --bmc1_ucm                              false
% 3.65/1.01  --bmc1_add_unsat_core                   none
% 3.65/1.01  --bmc1_unsat_core_children              false
% 3.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.01  --bmc1_out_stat                         full
% 3.65/1.01  --bmc1_ground_init                      false
% 3.65/1.01  --bmc1_pre_inst_next_state              false
% 3.65/1.01  --bmc1_pre_inst_state                   false
% 3.65/1.01  --bmc1_pre_inst_reach_state             false
% 3.65/1.01  --bmc1_out_unsat_core                   false
% 3.65/1.01  --bmc1_aig_witness_out                  false
% 3.65/1.01  --bmc1_verbose                          false
% 3.65/1.01  --bmc1_dump_clauses_tptp                false
% 3.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.01  --bmc1_dump_file                        -
% 3.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.01  --bmc1_ucm_extend_mode                  1
% 3.65/1.01  --bmc1_ucm_init_mode                    2
% 3.65/1.01  --bmc1_ucm_cone_mode                    none
% 3.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.01  --bmc1_ucm_relax_model                  4
% 3.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.01  --bmc1_ucm_layered_model                none
% 3.65/1.01  --bmc1_ucm_max_lemma_size               10
% 3.65/1.01  
% 3.65/1.01  ------ AIG Options
% 3.65/1.01  
% 3.65/1.01  --aig_mode                              false
% 3.65/1.01  
% 3.65/1.01  ------ Instantiation Options
% 3.65/1.01  
% 3.65/1.01  --instantiation_flag                    true
% 3.65/1.01  --inst_sos_flag                         true
% 3.65/1.01  --inst_sos_phase                        true
% 3.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel_side                     num_symb
% 3.65/1.01  --inst_solver_per_active                1400
% 3.65/1.01  --inst_solver_calls_frac                1.
% 3.65/1.01  --inst_passive_queue_type               priority_queues
% 3.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.01  --inst_passive_queues_freq              [25;2]
% 3.65/1.01  --inst_dismatching                      true
% 3.65/1.01  --inst_eager_unprocessed_to_passive     true
% 3.65/1.01  --inst_prop_sim_given                   true
% 3.65/1.01  --inst_prop_sim_new                     false
% 3.65/1.01  --inst_subs_new                         false
% 3.65/1.01  --inst_eq_res_simp                      false
% 3.65/1.01  --inst_subs_given                       false
% 3.65/1.01  --inst_orphan_elimination               true
% 3.65/1.01  --inst_learning_loop_flag               true
% 3.65/1.01  --inst_learning_start                   3000
% 3.65/1.01  --inst_learning_factor                  2
% 3.65/1.01  --inst_start_prop_sim_after_learn       3
% 3.65/1.01  --inst_sel_renew                        solver
% 3.65/1.01  --inst_lit_activity_flag                true
% 3.65/1.01  --inst_restr_to_given                   false
% 3.65/1.01  --inst_activity_threshold               500
% 3.65/1.01  --inst_out_proof                        true
% 3.65/1.01  
% 3.65/1.01  ------ Resolution Options
% 3.65/1.01  
% 3.65/1.01  --resolution_flag                       true
% 3.65/1.01  --res_lit_sel                           adaptive
% 3.65/1.01  --res_lit_sel_side                      none
% 3.65/1.01  --res_ordering                          kbo
% 3.65/1.01  --res_to_prop_solver                    active
% 3.65/1.01  --res_prop_simpl_new                    false
% 3.65/1.01  --res_prop_simpl_given                  true
% 3.65/1.01  --res_passive_queue_type                priority_queues
% 3.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.01  --res_passive_queues_freq               [15;5]
% 3.65/1.01  --res_forward_subs                      full
% 3.65/1.01  --res_backward_subs                     full
% 3.65/1.01  --res_forward_subs_resolution           true
% 3.65/1.01  --res_backward_subs_resolution          true
% 3.65/1.01  --res_orphan_elimination                true
% 3.65/1.01  --res_time_limit                        2.
% 3.65/1.01  --res_out_proof                         true
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Options
% 3.65/1.01  
% 3.65/1.01  --superposition_flag                    true
% 3.65/1.01  --sup_passive_queue_type                priority_queues
% 3.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.01  --demod_completeness_check              fast
% 3.65/1.01  --demod_use_ground                      true
% 3.65/1.01  --sup_to_prop_solver                    passive
% 3.65/1.01  --sup_prop_simpl_new                    true
% 3.65/1.01  --sup_prop_simpl_given                  true
% 3.65/1.01  --sup_fun_splitting                     true
% 3.65/1.01  --sup_smt_interval                      50000
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Simplification Setup
% 3.65/1.01  
% 3.65/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/1.01  --sup_immed_triv                        [TrivRules]
% 3.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_immed_bw_main                     []
% 3.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_input_bw                          []
% 3.65/1.01  
% 3.65/1.01  ------ Combination Options
% 3.65/1.01  
% 3.65/1.01  --comb_res_mult                         3
% 3.65/1.01  --comb_sup_mult                         2
% 3.65/1.01  --comb_inst_mult                        10
% 3.65/1.01  
% 3.65/1.01  ------ Debug Options
% 3.65/1.01  
% 3.65/1.01  --dbg_backtrace                         false
% 3.65/1.01  --dbg_dump_prop_clauses                 false
% 3.65/1.01  --dbg_dump_prop_clauses_file            -
% 3.65/1.01  --dbg_out_stat                          false
% 3.65/1.01  ------ Parsing...
% 3.65/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.01  ------ Proving...
% 3.65/1.01  ------ Problem Properties 
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  clauses                                 19
% 3.65/1.01  conjectures                             2
% 3.65/1.01  EPR                                     1
% 3.65/1.01  Horn                                    14
% 3.65/1.01  unary                                   3
% 3.65/1.01  binary                                  2
% 3.65/1.01  lits                                    55
% 3.65/1.01  lits eq                                 5
% 3.65/1.01  fd_pure                                 0
% 3.65/1.01  fd_pseudo                               0
% 3.65/1.01  fd_cond                                 0
% 3.65/1.01  fd_pseudo_cond                          2
% 3.65/1.01  AC symbols                              0
% 3.65/1.01  
% 3.65/1.01  ------ Schedule dynamic 5 is on 
% 3.65/1.01  
% 3.65/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  ------ 
% 3.65/1.01  Current options:
% 3.65/1.01  ------ 
% 3.65/1.01  
% 3.65/1.01  ------ Input Options
% 3.65/1.01  
% 3.65/1.01  --out_options                           all
% 3.65/1.01  --tptp_safe_out                         true
% 3.65/1.01  --problem_path                          ""
% 3.65/1.01  --include_path                          ""
% 3.65/1.01  --clausifier                            res/vclausify_rel
% 3.65/1.01  --clausifier_options                    ""
% 3.65/1.01  --stdin                                 false
% 3.65/1.01  --stats_out                             all
% 3.65/1.01  
% 3.65/1.01  ------ General Options
% 3.65/1.01  
% 3.65/1.01  --fof                                   false
% 3.65/1.01  --time_out_real                         305.
% 3.65/1.01  --time_out_virtual                      -1.
% 3.65/1.01  --symbol_type_check                     false
% 3.65/1.01  --clausify_out                          false
% 3.65/1.01  --sig_cnt_out                           false
% 3.65/1.01  --trig_cnt_out                          false
% 3.65/1.01  --trig_cnt_out_tolerance                1.
% 3.65/1.01  --trig_cnt_out_sk_spl                   false
% 3.65/1.01  --abstr_cl_out                          false
% 3.65/1.01  
% 3.65/1.01  ------ Global Options
% 3.65/1.01  
% 3.65/1.01  --schedule                              default
% 3.65/1.01  --add_important_lit                     false
% 3.65/1.01  --prop_solver_per_cl                    1000
% 3.65/1.01  --min_unsat_core                        false
% 3.65/1.01  --soft_assumptions                      false
% 3.65/1.01  --soft_lemma_size                       3
% 3.65/1.01  --prop_impl_unit_size                   0
% 3.65/1.01  --prop_impl_unit                        []
% 3.65/1.01  --share_sel_clauses                     true
% 3.65/1.01  --reset_solvers                         false
% 3.65/1.01  --bc_imp_inh                            [conj_cone]
% 3.65/1.01  --conj_cone_tolerance                   3.
% 3.65/1.01  --extra_neg_conj                        none
% 3.65/1.01  --large_theory_mode                     true
% 3.65/1.01  --prolific_symb_bound                   200
% 3.65/1.01  --lt_threshold                          2000
% 3.65/1.01  --clause_weak_htbl                      true
% 3.65/1.01  --gc_record_bc_elim                     false
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing Options
% 3.65/1.01  
% 3.65/1.01  --preprocessing_flag                    true
% 3.65/1.01  --time_out_prep_mult                    0.1
% 3.65/1.01  --splitting_mode                        input
% 3.65/1.01  --splitting_grd                         true
% 3.65/1.01  --splitting_cvd                         false
% 3.65/1.01  --splitting_cvd_svl                     false
% 3.65/1.01  --splitting_nvd                         32
% 3.65/1.01  --sub_typing                            true
% 3.65/1.01  --prep_gs_sim                           true
% 3.65/1.01  --prep_unflatten                        true
% 3.65/1.01  --prep_res_sim                          true
% 3.65/1.01  --prep_upred                            true
% 3.65/1.01  --prep_sem_filter                       exhaustive
% 3.65/1.01  --prep_sem_filter_out                   false
% 3.65/1.01  --pred_elim                             true
% 3.65/1.01  --res_sim_input                         true
% 3.65/1.01  --eq_ax_congr_red                       true
% 3.65/1.01  --pure_diseq_elim                       true
% 3.65/1.01  --brand_transform                       false
% 3.65/1.01  --non_eq_to_eq                          false
% 3.65/1.01  --prep_def_merge                        true
% 3.65/1.01  --prep_def_merge_prop_impl              false
% 3.65/1.01  --prep_def_merge_mbd                    true
% 3.65/1.01  --prep_def_merge_tr_red                 false
% 3.65/1.01  --prep_def_merge_tr_cl                  false
% 3.65/1.01  --smt_preprocessing                     true
% 3.65/1.01  --smt_ac_axioms                         fast
% 3.65/1.01  --preprocessed_out                      false
% 3.65/1.01  --preprocessed_stats                    false
% 3.65/1.01  
% 3.65/1.01  ------ Abstraction refinement Options
% 3.65/1.01  
% 3.65/1.01  --abstr_ref                             []
% 3.65/1.01  --abstr_ref_prep                        false
% 3.65/1.01  --abstr_ref_until_sat                   false
% 3.65/1.01  --abstr_ref_sig_restrict                funpre
% 3.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.01  --abstr_ref_under                       []
% 3.65/1.01  
% 3.65/1.01  ------ SAT Options
% 3.65/1.01  
% 3.65/1.01  --sat_mode                              false
% 3.65/1.01  --sat_fm_restart_options                ""
% 3.65/1.01  --sat_gr_def                            false
% 3.65/1.01  --sat_epr_types                         true
% 3.65/1.01  --sat_non_cyclic_types                  false
% 3.65/1.01  --sat_finite_models                     false
% 3.65/1.01  --sat_fm_lemmas                         false
% 3.65/1.01  --sat_fm_prep                           false
% 3.65/1.01  --sat_fm_uc_incr                        true
% 3.65/1.01  --sat_out_model                         small
% 3.65/1.01  --sat_out_clauses                       false
% 3.65/1.01  
% 3.65/1.01  ------ QBF Options
% 3.65/1.01  
% 3.65/1.01  --qbf_mode                              false
% 3.65/1.01  --qbf_elim_univ                         false
% 3.65/1.01  --qbf_dom_inst                          none
% 3.65/1.01  --qbf_dom_pre_inst                      false
% 3.65/1.01  --qbf_sk_in                             false
% 3.65/1.01  --qbf_pred_elim                         true
% 3.65/1.01  --qbf_split                             512
% 3.65/1.01  
% 3.65/1.01  ------ BMC1 Options
% 3.65/1.01  
% 3.65/1.01  --bmc1_incremental                      false
% 3.65/1.01  --bmc1_axioms                           reachable_all
% 3.65/1.01  --bmc1_min_bound                        0
% 3.65/1.01  --bmc1_max_bound                        -1
% 3.65/1.01  --bmc1_max_bound_default                -1
% 3.65/1.01  --bmc1_symbol_reachability              true
% 3.65/1.01  --bmc1_property_lemmas                  false
% 3.65/1.01  --bmc1_k_induction                      false
% 3.65/1.01  --bmc1_non_equiv_states                 false
% 3.65/1.01  --bmc1_deadlock                         false
% 3.65/1.01  --bmc1_ucm                              false
% 3.65/1.01  --bmc1_add_unsat_core                   none
% 3.65/1.01  --bmc1_unsat_core_children              false
% 3.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.01  --bmc1_out_stat                         full
% 3.65/1.01  --bmc1_ground_init                      false
% 3.65/1.01  --bmc1_pre_inst_next_state              false
% 3.65/1.01  --bmc1_pre_inst_state                   false
% 3.65/1.01  --bmc1_pre_inst_reach_state             false
% 3.65/1.01  --bmc1_out_unsat_core                   false
% 3.65/1.01  --bmc1_aig_witness_out                  false
% 3.65/1.01  --bmc1_verbose                          false
% 3.65/1.01  --bmc1_dump_clauses_tptp                false
% 3.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.01  --bmc1_dump_file                        -
% 3.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.01  --bmc1_ucm_extend_mode                  1
% 3.65/1.01  --bmc1_ucm_init_mode                    2
% 3.65/1.01  --bmc1_ucm_cone_mode                    none
% 3.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.01  --bmc1_ucm_relax_model                  4
% 3.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.01  --bmc1_ucm_layered_model                none
% 3.65/1.01  --bmc1_ucm_max_lemma_size               10
% 3.65/1.01  
% 3.65/1.01  ------ AIG Options
% 3.65/1.01  
% 3.65/1.01  --aig_mode                              false
% 3.65/1.01  
% 3.65/1.01  ------ Instantiation Options
% 3.65/1.01  
% 3.65/1.01  --instantiation_flag                    true
% 3.65/1.01  --inst_sos_flag                         true
% 3.65/1.01  --inst_sos_phase                        true
% 3.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.01  --inst_lit_sel_side                     none
% 3.65/1.01  --inst_solver_per_active                1400
% 3.65/1.01  --inst_solver_calls_frac                1.
% 3.65/1.01  --inst_passive_queue_type               priority_queues
% 3.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.01  --inst_passive_queues_freq              [25;2]
% 3.65/1.01  --inst_dismatching                      true
% 3.65/1.01  --inst_eager_unprocessed_to_passive     true
% 3.65/1.01  --inst_prop_sim_given                   true
% 3.65/1.01  --inst_prop_sim_new                     false
% 3.65/1.01  --inst_subs_new                         false
% 3.65/1.01  --inst_eq_res_simp                      false
% 3.65/1.01  --inst_subs_given                       false
% 3.65/1.01  --inst_orphan_elimination               true
% 3.65/1.01  --inst_learning_loop_flag               true
% 3.65/1.01  --inst_learning_start                   3000
% 3.65/1.01  --inst_learning_factor                  2
% 3.65/1.01  --inst_start_prop_sim_after_learn       3
% 3.65/1.01  --inst_sel_renew                        solver
% 3.65/1.01  --inst_lit_activity_flag                true
% 3.65/1.01  --inst_restr_to_given                   false
% 3.65/1.01  --inst_activity_threshold               500
% 3.65/1.01  --inst_out_proof                        true
% 3.65/1.01  
% 3.65/1.01  ------ Resolution Options
% 3.65/1.01  
% 3.65/1.01  --resolution_flag                       false
% 3.65/1.01  --res_lit_sel                           adaptive
% 3.65/1.01  --res_lit_sel_side                      none
% 3.65/1.01  --res_ordering                          kbo
% 3.65/1.01  --res_to_prop_solver                    active
% 3.65/1.01  --res_prop_simpl_new                    false
% 3.65/1.01  --res_prop_simpl_given                  true
% 3.65/1.01  --res_passive_queue_type                priority_queues
% 3.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.01  --res_passive_queues_freq               [15;5]
% 3.65/1.01  --res_forward_subs                      full
% 3.65/1.01  --res_backward_subs                     full
% 3.65/1.01  --res_forward_subs_resolution           true
% 3.65/1.01  --res_backward_subs_resolution          true
% 3.65/1.01  --res_orphan_elimination                true
% 3.65/1.01  --res_time_limit                        2.
% 3.65/1.01  --res_out_proof                         true
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Options
% 3.65/1.01  
% 3.65/1.01  --superposition_flag                    true
% 3.65/1.01  --sup_passive_queue_type                priority_queues
% 3.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.01  --demod_completeness_check              fast
% 3.65/1.01  --demod_use_ground                      true
% 3.65/1.01  --sup_to_prop_solver                    passive
% 3.65/1.01  --sup_prop_simpl_new                    true
% 3.65/1.01  --sup_prop_simpl_given                  true
% 3.65/1.01  --sup_fun_splitting                     true
% 3.65/1.01  --sup_smt_interval                      50000
% 3.65/1.01  
% 3.65/1.01  ------ Superposition Simplification Setup
% 3.65/1.01  
% 3.65/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/1.01  --sup_immed_triv                        [TrivRules]
% 3.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_immed_bw_main                     []
% 3.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.01  --sup_input_bw                          []
% 3.65/1.01  
% 3.65/1.01  ------ Combination Options
% 3.65/1.01  
% 3.65/1.01  --comb_res_mult                         3
% 3.65/1.01  --comb_sup_mult                         2
% 3.65/1.01  --comb_inst_mult                        10
% 3.65/1.01  
% 3.65/1.01  ------ Debug Options
% 3.65/1.01  
% 3.65/1.01  --dbg_backtrace                         false
% 3.65/1.01  --dbg_dump_prop_clauses                 false
% 3.65/1.01  --dbg_dump_prop_clauses_file            -
% 3.65/1.01  --dbg_out_stat                          false
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  ------ Proving...
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  % SZS status Theorem for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  fof(f8,conjecture,(
% 3.65/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f9,negated_conjecture,(
% 3.65/1.01    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 3.65/1.01    inference(negated_conjecture,[],[f8])).
% 3.65/1.01  
% 3.65/1.01  fof(f18,plain,(
% 3.65/1.01    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 3.65/1.01    inference(ennf_transformation,[],[f9])).
% 3.65/1.01  
% 3.65/1.01  fof(f33,plain,(
% 3.65/1.01    ( ! [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~r1_lattice3(X0,k1_xboole_0,sK4) | ~r2_lattice3(X0,k1_xboole_0,sK4)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f32,plain,(
% 3.65/1.01    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : ((~r1_lattice3(sK3,k1_xboole_0,X1) | ~r2_lattice3(sK3,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3))),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f34,plain,(
% 3.65/1.01    ((~r1_lattice3(sK3,k1_xboole_0,sK4) | ~r2_lattice3(sK3,k1_xboole_0,sK4)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3)),
% 3.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f33,f32])).
% 3.65/1.01  
% 3.65/1.01  fof(f53,plain,(
% 3.65/1.01    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.65/1.01    inference(cnf_transformation,[],[f34])).
% 3.65/1.01  
% 3.65/1.01  fof(f6,axiom,(
% 3.65/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f14,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(ennf_transformation,[],[f6])).
% 3.65/1.01  
% 3.65/1.01  fof(f15,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(flattening,[],[f14])).
% 3.65/1.01  
% 3.65/1.01  fof(f24,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(nnf_transformation,[],[f15])).
% 3.65/1.01  
% 3.65/1.01  fof(f25,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(rectify,[],[f24])).
% 3.65/1.01  
% 3.65/1.01  fof(f26,plain,(
% 3.65/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f27,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.65/1.01  
% 3.65/1.01  fof(f46,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f27])).
% 3.65/1.01  
% 3.65/1.01  fof(f52,plain,(
% 3.65/1.01    l1_orders_2(sK3)),
% 3.65/1.01    inference(cnf_transformation,[],[f34])).
% 3.65/1.01  
% 3.65/1.01  fof(f3,axiom,(
% 3.65/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f40,plain,(
% 3.65/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f3])).
% 3.65/1.01  
% 3.65/1.01  fof(f2,axiom,(
% 3.65/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f10,plain,(
% 3.65/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/1.01    inference(ennf_transformation,[],[f2])).
% 3.65/1.01  
% 3.65/1.01  fof(f39,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f10])).
% 3.65/1.01  
% 3.65/1.01  fof(f1,axiom,(
% 3.65/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f19,plain,(
% 3.65/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.65/1.01    inference(nnf_transformation,[],[f1])).
% 3.65/1.01  
% 3.65/1.01  fof(f20,plain,(
% 3.65/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.65/1.01    inference(rectify,[],[f19])).
% 3.65/1.01  
% 3.65/1.01  fof(f21,plain,(
% 3.65/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f22,plain,(
% 3.65/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.65/1.01  
% 3.65/1.01  fof(f35,plain,(
% 3.65/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.65/1.01    inference(cnf_transformation,[],[f22])).
% 3.65/1.01  
% 3.65/1.01  fof(f57,plain,(
% 3.65/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.65/1.01    inference(equality_resolution,[],[f35])).
% 3.65/1.01  
% 3.65/1.01  fof(f44,plain,(
% 3.65/1.01    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f27])).
% 3.65/1.01  
% 3.65/1.01  fof(f7,axiom,(
% 3.65/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f16,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(ennf_transformation,[],[f7])).
% 3.65/1.01  
% 3.65/1.01  fof(f17,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(flattening,[],[f16])).
% 3.65/1.01  
% 3.65/1.01  fof(f28,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(nnf_transformation,[],[f17])).
% 3.65/1.01  
% 3.65/1.01  fof(f29,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(rectify,[],[f28])).
% 3.65/1.01  
% 3.65/1.01  fof(f30,plain,(
% 3.65/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f31,plain,(
% 3.65/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.65/1.01  
% 3.65/1.01  fof(f50,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f31])).
% 3.65/1.01  
% 3.65/1.01  fof(f54,plain,(
% 3.65/1.01    ~r1_lattice3(sK3,k1_xboole_0,sK4) | ~r2_lattice3(sK3,k1_xboole_0,sK4)),
% 3.65/1.01    inference(cnf_transformation,[],[f34])).
% 3.65/1.01  
% 3.65/1.01  fof(f49,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f31])).
% 3.65/1.01  
% 3.65/1.01  fof(f4,axiom,(
% 3.65/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f11,plain,(
% 3.65/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.65/1.01    inference(ennf_transformation,[],[f4])).
% 3.65/1.01  
% 3.65/1.01  fof(f12,plain,(
% 3.65/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.65/1.01    inference(flattening,[],[f11])).
% 3.65/1.01  
% 3.65/1.01  fof(f41,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f12])).
% 3.65/1.01  
% 3.65/1.01  fof(f36,plain,(
% 3.65/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.65/1.01    inference(cnf_transformation,[],[f22])).
% 3.65/1.01  
% 3.65/1.01  fof(f55,plain,(
% 3.65/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.65/1.01    inference(equality_resolution,[],[f36])).
% 3.65/1.01  
% 3.65/1.01  fof(f56,plain,(
% 3.65/1.01    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.65/1.01    inference(equality_resolution,[],[f55])).
% 3.65/1.01  
% 3.65/1.01  fof(f47,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f27])).
% 3.65/1.01  
% 3.65/1.01  fof(f51,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f31])).
% 3.65/1.01  
% 3.65/1.01  fof(f5,axiom,(
% 3.65/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 3.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f13,plain,(
% 3.65/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(ennf_transformation,[],[f5])).
% 3.65/1.01  
% 3.65/1.01  fof(f23,plain,(
% 3.65/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.65/1.01    inference(nnf_transformation,[],[f13])).
% 3.65/1.01  
% 3.65/1.01  fof(f43,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f23])).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1435,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2162,plain,
% 3.65/1.01      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2578,plain,
% 3.65/1.01      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2162]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_8691,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) != sK4
% 3.65/1.01      | sK4 = sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK4 != sK4 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2578]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_7623,plain,
% 3.65/1.01      ( X0 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK4 = X0
% 3.65/1.01      | sK4 != sK1(sK3,k1_xboole_0,sK4) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2162]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_7625,plain,
% 3.65/1.01      ( sK4 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK4 = sK3
% 3.65/1.01      | sK3 != sK1(sK3,k1_xboole_0,sK4) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_7623]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_18,negated_conjecture,
% 3.65/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1789,plain,
% 3.65/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_10,plain,
% 3.65/1.01      ( r1_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_19,negated_conjecture,
% 3.65/1.01      ( l1_orders_2(sK3) ),
% 3.65/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_326,plain,
% 3.65/1.01      ( r1_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_327,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | r2_hidden(sK1(sK3,X0,X1),X0) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_326]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1782,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,X0,X1),X0) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.65/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1792,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4,plain,
% 3.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.01      | ~ r2_hidden(X2,X0)
% 3.65/1.01      | r2_hidden(X2,X1) ),
% 3.65/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1793,plain,
% 3.65/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.65/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.65/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2600,plain,
% 3.65/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.65/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1792,c_1793]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2766,plain,
% 3.65/1.01      ( r1_lattice3(sK3,k1_xboole_0,X0) = iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,X0),X1) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1782,c_2600]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3,plain,
% 3.65/1.01      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.65/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1794,plain,
% 3.65/1.01      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2964,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,X0) = X1
% 3.65/1.01      | r1_lattice3(sK3,k1_xboole_0,X0) = iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_2766,c_1794]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4446,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) = X0
% 3.65/1.01      | r1_lattice3(sK3,k1_xboole_0,sK4) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1789,c_2964]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_12,plain,
% 3.65/1.01      ( ~ r1_lattice3(X0,X1,X2)
% 3.65/1.01      | r1_orders_2(X0,X2,X3)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.65/1.01      | ~ r2_hidden(X3,X1)
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_290,plain,
% 3.65/1.01      ( ~ r1_lattice3(X0,X1,X2)
% 3.65/1.01      | r1_orders_2(X0,X2,X3)
% 3.65/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | ~ r2_hidden(X3,X1)
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_291,plain,
% 3.65/1.01      ( ~ r1_lattice3(sK3,X0,X1)
% 3.65/1.01      | r1_orders_2(sK3,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.65/1.01      | ~ r2_hidden(X2,X0) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_290]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1784,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,X1,X2) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(X2,X0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2176,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK4) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK4,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1789,c_1784]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2181,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK4) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK4,sK4) = iProver_top
% 3.65/1.01      | r2_hidden(sK4,X0) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1789,c_2176]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4537,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) = X0
% 3.65/1.01      | r1_orders_2(sK3,sK4,sK4) = iProver_top
% 3.65/1.01      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_4446,c_2181]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_14,plain,
% 3.65/1.01      ( r2_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_260,plain,
% 3.65/1.01      ( r2_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_261,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | r2_hidden(sK2(sK3,X0,X1),X0) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_260]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1786,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK2(sK3,X0,X1),X0) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2765,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,X0) = iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK2(sK3,k1_xboole_0,X0),X1) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1786,c_2600]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2914,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,X0) = X1
% 3.65/1.01      | r2_lattice3(sK3,k1_xboole_0,X0) = iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_2765,c_1794]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3976,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = X0
% 3.65/1.01      | r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1789,c_2914]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_17,negated_conjecture,
% 3.65/1.01      ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | ~ r1_lattice3(sK3,k1_xboole_0,sK4) ),
% 3.65/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1790,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4) != iProver_top
% 3.65/1.01      | r1_lattice3(sK3,k1_xboole_0,sK4) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3993,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = X0
% 3.65/1.01      | r1_lattice3(sK3,k1_xboole_0,sK4) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_3976,c_1790]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4536,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = X0 | sK1(sK3,k1_xboole_0,sK4) = X1 ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_4446,c_3993]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4662,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) != X0 | sK1(sK3,k1_xboole_0,sK4) = X0 ),
% 3.65/1.01      inference(equality_factoring,[status(thm)],[c_4536]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5004,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) = X0 ),
% 3.65/1.01      inference(global_propositional_subsumption,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_4537,c_3993,c_4446,c_4662]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_15,plain,
% 3.65/1.01      ( r2_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_245,plain,
% 3.65/1.01      ( r2_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_246,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_245]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1787,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5012,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(demodulation,[status(thm)],[c_5004,c_1787]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2216,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2217,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2216]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6,plain,
% 3.65/1.01      ( m1_subset_1(X0,X1)
% 3.65/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.65/1.01      | ~ r2_hidden(X0,X2) ),
% 3.65/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1839,plain,
% 3.65/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/1.01      | ~ r2_hidden(X0,X1) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1958,plain,
% 3.65/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/1.01      | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1839]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2794,plain,
% 3.65/1.01      ( m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/1.01      | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1958]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2795,plain,
% 3.65/1.01      ( m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top
% 3.65/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5013,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) = iProver_top ),
% 3.65/1.01      inference(demodulation,[status(thm)],[c_5004,c_1786]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5423,plain,
% 3.65/1.01      ( r1_lattice3(sK3,k1_xboole_0,sK4) != iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5013,c_1790]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_21,plain,
% 3.65/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1870,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK4)
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | r2_hidden(sK1(sK3,X0,sK4),X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_327]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1931,plain,
% 3.65/1.01      ( r1_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1870]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1932,plain,
% 3.65/1.01      ( r1_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_1931]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5714,plain,
% 3.65/1.01      ( r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 3.65/1.01      inference(global_propositional_subsumption,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_5423,c_21,c_1932]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6126,plain,
% 3.65/1.01      ( m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(global_propositional_subsumption,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_5012,c_21,c_1932,c_2217,c_2795,c_5423]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6130,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK4) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4)) = iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_6126,c_2176]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_56,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_58,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_56]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_61,plain,
% 3.65/1.01      ( ~ r2_hidden(sK3,k1_tarski(sK3)) | sK3 = sK3 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2,plain,
% 3.65/1.01      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.65/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_64,plain,
% 3.65/1.01      ( r2_hidden(sK3,k1_tarski(sK3)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_9,plain,
% 3.65/1.01      ( r1_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_341,plain,
% 3.65/1.01      ( r1_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_342,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1)
% 3.65/1.01      | ~ r1_orders_2(sK3,X1,sK1(sK3,X0,X1))
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_341]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_498,plain,
% 3.65/1.01      ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | ~ r1_orders_2(sK3,X0,sK1(sK3,X1,X0))
% 3.65/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/1.01      | sK4 != X0
% 3.65/1.01      | sK3 != sK3
% 3.65/1.01      | k1_xboole_0 != X1 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_342]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_499,plain,
% 3.65/1.01      ( ~ r2_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | ~ r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4))
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_498]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_500,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1440,plain,
% 3.65/1.01      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.65/1.01      theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1449,plain,
% 3.65/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1440]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1834,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,sK4)
% 3.65/1.01      | m1_subset_1(sK2(sK3,X0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_246]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1914,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1834]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1915,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
% 3.65/1.01      | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) = iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1907,plain,
% 3.65/1.01      ( ~ r1_lattice3(sK3,X0,sK4)
% 3.65/1.01      | r1_orders_2(sK3,sK4,X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | ~ r2_hidden(X1,X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_291]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1985,plain,
% 3.65/1.01      ( ~ r1_lattice3(sK3,X0,sK4)
% 3.65/1.01      | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4))
% 3.65/1.01      | ~ m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1907]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2041,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK4) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK4,sK1(sK3,k1_xboole_0,sK4)) = iProver_top
% 3.65/1.01      | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_1985]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_13,plain,
% 3.65/1.01      ( r2_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_275,plain,
% 3.65/1.01      ( r2_lattice3(X0,X1,X2)
% 3.65/1.01      | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_276,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,X1)
% 3.65/1.01      | ~ r1_orders_2(sK3,sK2(sK3,X0,X1),X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_275]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1863,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,sK4)
% 3.65/1.01      | ~ r1_orders_2(sK3,sK2(sK3,X0,sK4),sK4)
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_276]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2066,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | ~ r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4)
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1863]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2068,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4) != iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2066]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1856,plain,
% 3.65/1.01      ( r2_lattice3(sK3,X0,sK4)
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | r2_hidden(sK2(sK3,X0,sK4),X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_261]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2065,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1856]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2070,plain,
% 3.65/1.01      ( r2_lattice3(sK3,k1_xboole_0,sK4) = iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2065]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1436,plain,
% 3.65/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.65/1.01      theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2152,plain,
% 3.65/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2153,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | sK4 != X2
% 3.65/1.01      | r2_hidden(X2,X1) != iProver_top
% 3.65/1.01      | r2_hidden(sK4,X0) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2152]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2155,plain,
% 3.65/1.01      ( sK4 != sK3
% 3.65/1.01      | sK3 != sK3
% 3.65/1.01      | r2_hidden(sK4,sK3) = iProver_top
% 3.65/1.01      | r2_hidden(sK3,sK3) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2153]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2303,plain,
% 3.65/1.01      ( ~ r2_hidden(X0,k1_tarski(sK4)) | X0 = sK4 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2304,plain,
% 3.65/1.01      ( X0 = sK4 | r2_hidden(X0,k1_tarski(sK4)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2306,plain,
% 3.65/1.01      ( sK3 = sK4 | r2_hidden(sK3,k1_tarski(sK4)) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2304]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1437,plain,
% 3.65/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.65/1.01      theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1844,plain,
% 3.65/1.01      ( ~ m1_subset_1(X0,X1)
% 3.65/1.01      | m1_subset_1(X2,u1_struct_0(sK3))
% 3.65/1.01      | X2 != X0
% 3.65/1.01      | u1_struct_0(sK3) != X1 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1437]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1979,plain,
% 3.65/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | X1 != X0
% 3.65/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1844]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2327,plain,
% 3.65/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | X0 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1979]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2329,plain,
% 3.65/1.01      ( X0 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.65/1.01      | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2327]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2331,plain,
% 3.65/1.01      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/1.01      | sK3 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | m1_subset_1(sK1(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK3,u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2329]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2360,plain,
% 3.65/1.01      ( r2_hidden(sK4,k1_tarski(sK4)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2163,plain,
% 3.65/1.01      ( ~ r2_hidden(sK4,k1_tarski(X0)) | sK4 = X0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2468,plain,
% 3.65/1.01      ( ~ r2_hidden(sK4,k1_tarski(sK4)) | sK4 = sK4 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2163]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2510,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | X0 = sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK1(sK3,k1_xboole_0,sK4) != X1 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2511,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) != sK3
% 3.65/1.01      | sK3 = sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK3 != sK3 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2510]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2579,plain,
% 3.65/1.01      ( sK4 != sK4 | sK4 = sK3 | sK3 != sK4 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2578]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2374,plain,
% 3.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/1.01      | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0)
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X1) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2736,plain,
% 3.65/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0)
% 3.65/1.01      | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2374]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2737,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) = iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2736]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2739,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),sK3) = iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2737]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3586,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | X0 = sK2(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK2(sK3,k1_xboole_0,sK4) != X1 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3587,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) != sK3
% 3.65/1.01      | sK3 = sK2(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK3 != sK3 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3586]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3599,plain,
% 3.65/1.01      ( r2_hidden(X0,X1)
% 3.65/1.01      | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),X2)
% 3.65/1.01      | X1 != X2
% 3.65/1.01      | X0 != sK1(sK3,k1_xboole_0,sK4) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3600,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | X2 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | r2_hidden(X2,X0) = iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),X1) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3599]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3602,plain,
% 3.65/1.01      ( sK3 != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK3 != sK3
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),sK3) != iProver_top
% 3.65/1.01      | r2_hidden(sK3,sK3) = iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3600]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2075,plain,
% 3.65/1.01      ( ~ r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4))
% 3.65/1.01      | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | ~ r2_hidden(X1,X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_291]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3767,plain,
% 3.65/1.01      ( ~ r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4))
% 3.65/1.01      | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4)
% 3.65/1.01      | ~ m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.65/1.01      | ~ r2_hidden(sK4,X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2075]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3768,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4)) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4) = iProver_top
% 3.65/1.01      | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK4,X0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3767]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3770,plain,
% 3.65/1.01      ( r1_lattice3(sK3,sK3,sK2(sK3,k1_xboole_0,sK4)) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK2(sK3,k1_xboole_0,sK4),sK4) = iProver_top
% 3.65/1.01      | m1_subset_1(sK2(sK3,k1_xboole_0,sK4),u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK4,sK3) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3768]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2490,plain,
% 3.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tarski(sK4)))
% 3.65/1.01      | ~ r2_hidden(X1,X0)
% 3.65/1.01      | r2_hidden(X1,k1_tarski(sK4)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4162,plain,
% 3.65/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4)))
% 3.65/1.01      | r2_hidden(X0,k1_tarski(sK4))
% 3.65/1.01      | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2490]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4163,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) != iProver_top
% 3.65/1.01      | r2_hidden(X0,k1_tarski(sK4)) = iProver_top
% 3.65/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_4162]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4165,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) != iProver_top
% 3.65/1.01      | r2_hidden(sK3,k1_tarski(sK4)) = iProver_top
% 3.65/1.01      | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_4163]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4660,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK1(sK3,k1_xboole_0,sK4) = X0 ),
% 3.65/1.01      inference(equality_factoring,[status(thm)],[c_4536]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4904,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK1(sK3,k1_xboole_0,sK4) = sK3 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_4660]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4661,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK1(sK3,k1_xboole_0,sK4) != X0 ),
% 3.65/1.01      inference(equality_factoring,[status(thm)],[c_4536]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4663,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = X0
% 3.65/1.01      | sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4) ),
% 3.65/1.01      inference(equality_factoring,[status(thm)],[c_4536]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4907,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) != sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK2(sK3,k1_xboole_0,sK4) = sK3 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_4663]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5606,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5607,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_5606]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5718,plain,
% 3.65/1.01      ( r2_hidden(sK1(sK3,k1_xboole_0,sK4),X0) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5714,c_2600]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_7,plain,
% 3.65/1.01      ( r1_orders_2(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/1.01      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.65/1.01      | ~ l1_orders_2(X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_374,plain,
% 3.65/1.01      ( r1_orders_2(X0,X1,X2)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/1.01      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_375,plain,
% 3.65/1.01      ( r1_orders_2(sK3,X0,X1)
% 3.65/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.65/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/1.01      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
% 3.65/1.01      inference(unflattening,[status(thm)],[c_374]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1779,plain,
% 3.65/1.01      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5082,plain,
% 3.65/1.01      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),u1_orders_2(sK3)) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5004,c_1779]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1980,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_1979]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5069,plain,
% 3.65/1.01      ( X0 = X1 ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5004,c_5004]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5301,plain,
% 3.65/1.01      ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r1_orders_2(sK3,X0,X1) = iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),u1_orders_2(sK3)) != iProver_top ),
% 3.65/1.01      inference(global_propositional_subsumption,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_5082,c_61,c_64,c_1449,c_1980,c_5069]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5302,plain,
% 3.65/1.01      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),u1_orders_2(sK3)) != iProver_top ),
% 3.65/1.01      inference(renaming,[status(thm)],[c_5301]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5814,plain,
% 3.65/1.01      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5718,c_5302]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5822,plain,
% 3.65/1.01      ( r1_orders_2(sK3,sK3,sK3) = iProver_top
% 3.65/1.01      | m1_subset_1(sK3,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_5814]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1795,plain,
% 3.65/1.01      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4602,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = X0
% 3.65/1.01      | r2_hidden(X1,sK1(sK3,k1_xboole_0,sK4)) = iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_4536,c_1795]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5627,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = X0 ),
% 3.65/1.01      inference(global_propositional_subsumption,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_4602,c_3993,c_4446,c_4661,c_4662,c_4663]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1781,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | r1_orders_2(sK3,X1,sK1(sK3,X0,X1)) != iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5650,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | r1_orders_2(sK3,X1,sK2(sK3,k1_xboole_0,sK4)) != iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5627,c_1781]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5825,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.65/1.01      | r1_orders_2(sK3,X1,X2) != iProver_top
% 3.65/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_5627,c_5650]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5827,plain,
% 3.65/1.01      ( r1_lattice3(sK3,sK3,sK3) = iProver_top
% 3.65/1.01      | r1_orders_2(sK3,sK3,sK3) != iProver_top
% 3.65/1.01      | m1_subset_1(sK3,u1_struct_0(sK3)) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_5825]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1441,plain,
% 3.65/1.01      ( ~ r1_lattice3(X0,X1,X2)
% 3.65/1.01      | r1_lattice3(X3,X4,X5)
% 3.65/1.01      | X3 != X0
% 3.65/1.01      | X4 != X1
% 3.65/1.01      | X5 != X2 ),
% 3.65/1.01      theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5901,plain,
% 3.65/1.01      ( ~ r1_lattice3(X0,X1,X2)
% 3.65/1.01      | r1_lattice3(sK3,X3,sK2(sK3,k1_xboole_0,sK4))
% 3.65/1.01      | X3 != X1
% 3.65/1.01      | sK2(sK3,k1_xboole_0,sK4) != X2
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1441]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5902,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | sK2(sK3,k1_xboole_0,sK4) != X2
% 3.65/1.01      | sK3 != X3
% 3.65/1.01      | r1_lattice3(X3,X1,X2) != iProver_top
% 3.65/1.01      | r1_lattice3(sK3,X0,sK2(sK3,k1_xboole_0,sK4)) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_5901]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5904,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) != sK3
% 3.65/1.01      | sK3 != sK3
% 3.65/1.01      | r1_lattice3(sK3,sK3,sK2(sK3,k1_xboole_0,sK4)) = iProver_top
% 3.65/1.01      | r1_lattice3(sK3,sK3,sK3) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_5902]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1434,plain,( X0 = X0 ),theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5989,plain,
% 3.65/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1434]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3520,plain,
% 3.65/1.01      ( r2_hidden(X0,X1)
% 3.65/1.01      | ~ r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0)
% 3.65/1.01      | X0 != sK2(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | X1 != k1_xboole_0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6251,plain,
% 3.65/1.01      ( r2_hidden(X0,k1_xboole_0)
% 3.65/1.01      | ~ r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0)
% 3.65/1.01      | X0 != sK2(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3520]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6252,plain,
% 3.65/1.01      ( X0 != sK2(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | k1_xboole_0 != k1_xboole_0
% 3.65/1.01      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.65/1.01      | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_6251]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6254,plain,
% 3.65/1.01      ( sK3 != sK2(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | k1_xboole_0 != k1_xboole_0
% 3.65/1.01      | r2_hidden(sK2(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top
% 3.65/1.01      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_6252]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6296,plain,
% 3.65/1.01      ( r1_lattice3(sK3,X0,sK4) != iProver_top ),
% 3.65/1.01      inference(global_propositional_subsumption,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_6130,c_21,c_56,c_58,c_61,c_64,c_500,c_1449,c_1915,
% 3.65/1.01                 c_1932,c_2041,c_2068,c_2070,c_2155,c_2217,c_2306,c_2331,
% 3.65/1.01                 c_2360,c_2468,c_2511,c_2579,c_2737,c_2739,c_2795,c_3587,
% 3.65/1.01                 c_3602,c_3770,c_3993,c_4165,c_4446,c_4904,c_4661,c_4662,
% 3.65/1.01                 c_4907,c_5423,c_5607,c_5822,c_5827,c_5904,c_5989,c_6254]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6299,plain,
% 3.65/1.01      ( r1_lattice3(sK3,sK3,sK4) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_6296]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3617,plain,
% 3.65/1.01      ( ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4))
% 3.65/1.01      | sK1(sK3,k1_xboole_0,sK4) = sK4 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2303]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3620,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) = sK4
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4)) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3617]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3616,plain,
% 3.65/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4)))
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4))
% 3.65/1.01      | ~ r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_2736]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3618,plain,
% 3.65/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK4))) != iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_tarski(sK4)) = iProver_top
% 3.65/1.01      | r2_hidden(sK1(sK3,k1_xboole_0,sK4),k1_xboole_0) != iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3616]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3333,plain,
% 3.65/1.01      ( ~ r1_lattice3(X0,X1,X2)
% 3.65/1.01      | r1_lattice3(sK3,X3,sK4)
% 3.65/1.01      | X3 != X1
% 3.65/1.01      | sK4 != X2
% 3.65/1.01      | sK3 != X0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_1441]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3334,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | sK4 != X2
% 3.65/1.01      | sK3 != X3
% 3.65/1.01      | r1_lattice3(X3,X1,X2) != iProver_top
% 3.65/1.01      | r1_lattice3(sK3,X0,sK4) = iProver_top ),
% 3.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3333]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3336,plain,
% 3.65/1.01      ( sK4 != sK3
% 3.65/1.01      | sK3 != sK3
% 3.65/1.01      | r1_lattice3(sK3,sK3,sK4) = iProver_top
% 3.65/1.01      | r1_lattice3(sK3,sK3,sK3) != iProver_top ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_3334]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_8699,plain,
% 3.65/1.01      ( sK1(sK3,k1_xboole_0,sK4) = sK3 ),
% 3.65/1.01      inference(grounding,[status(thm)],[c_5004:[bind(X0,$fot(sK3))]]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_8700,plain,
% 3.65/1.01      ( sK2(sK3,k1_xboole_0,sK4) = sK1(sK3,k1_xboole_0,sK4)
% 3.65/1.01      | sK1(sK3,k1_xboole_0,sK4) != sK3 ),
% 3.65/1.01      inference(grounding,[status(thm)],[c_4661:[bind(X0,$fot(sK3))]]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(contradiction,plain,
% 3.65/1.01      ( $false ),
% 3.65/1.01      inference(minisat,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_8691,c_7625,c_6299,c_5827,c_5822,c_5714,c_5607,c_8699,
% 3.65/1.01                 c_8700,c_4904,c_3620,c_3618,c_3336,c_2795,c_2511,c_2468,
% 3.65/1.01                 c_2360,c_2331,c_2217,c_1449,c_64,c_61]) ).
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  ------                               Statistics
% 3.65/1.01  
% 3.65/1.01  ------ General
% 3.65/1.01  
% 3.65/1.01  abstr_ref_over_cycles:                  0
% 3.65/1.01  abstr_ref_under_cycles:                 0
% 3.65/1.01  gc_basic_clause_elim:                   0
% 3.65/1.01  forced_gc_time:                         0
% 3.65/1.01  parsing_time:                           0.007
% 3.65/1.01  unif_index_cands_time:                  0.
% 3.65/1.01  unif_index_add_time:                    0.
% 3.65/1.01  orderings_time:                         0.
% 3.65/1.01  out_proof_time:                         0.015
% 3.65/1.01  total_time:                             0.296
% 3.65/1.01  num_of_symbols:                         49
% 3.65/1.01  num_of_terms:                           7686
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing
% 3.65/1.01  
% 3.65/1.01  num_of_splits:                          0
% 3.65/1.01  num_of_split_atoms:                     1
% 3.65/1.01  num_of_reused_defs:                     1
% 3.65/1.01  num_eq_ax_congr_red:                    34
% 3.65/1.01  num_of_sem_filtered_clauses:            1
% 3.65/1.01  num_of_subtypes:                        0
% 3.65/1.01  monotx_restored_types:                  0
% 3.65/1.01  sat_num_of_epr_types:                   0
% 3.65/1.01  sat_num_of_non_cyclic_types:            0
% 3.65/1.01  sat_guarded_non_collapsed_types:        0
% 3.65/1.01  num_pure_diseq_elim:                    0
% 3.65/1.01  simp_replaced_by:                       0
% 3.65/1.01  res_preprocessed:                       100
% 3.65/1.01  prep_upred:                             0
% 3.65/1.01  prep_unflattend:                        66
% 3.65/1.01  smt_new_axioms:                         0
% 3.65/1.01  pred_elim_cands:                        5
% 3.65/1.01  pred_elim:                              1
% 3.65/1.01  pred_elim_cl:                           1
% 3.65/1.01  pred_elim_cycles:                       7
% 3.65/1.01  merged_defs:                            0
% 3.65/1.01  merged_defs_ncl:                        0
% 3.65/1.01  bin_hyper_res:                          0
% 3.65/1.01  prep_cycles:                            4
% 3.65/1.01  pred_elim_time:                         0.014
% 3.65/1.01  splitting_time:                         0.
% 3.65/1.01  sem_filter_time:                        0.
% 3.65/1.01  monotx_time:                            0.
% 3.65/1.01  subtype_inf_time:                       0.
% 3.65/1.01  
% 3.65/1.01  ------ Problem properties
% 3.65/1.01  
% 3.65/1.01  clauses:                                19
% 3.65/1.01  conjectures:                            2
% 3.65/1.01  epr:                                    1
% 3.65/1.01  horn:                                   14
% 3.65/1.01  ground:                                 2
% 3.65/1.01  unary:                                  3
% 3.65/1.01  binary:                                 2
% 3.65/1.01  lits:                                   55
% 3.65/1.01  lits_eq:                                5
% 3.65/1.01  fd_pure:                                0
% 3.65/1.01  fd_pseudo:                              0
% 3.65/1.01  fd_cond:                                0
% 3.65/1.01  fd_pseudo_cond:                         2
% 3.65/1.01  ac_symbols:                             0
% 3.65/1.01  
% 3.65/1.01  ------ Propositional Solver
% 3.65/1.01  
% 3.65/1.01  prop_solver_calls:                      30
% 3.65/1.01  prop_fast_solver_calls:                 1371
% 3.65/1.01  smt_solver_calls:                       0
% 3.65/1.01  smt_fast_solver_calls:                  0
% 3.65/1.01  prop_num_of_clauses:                    4321
% 3.65/1.01  prop_preprocess_simplified:             7739
% 3.65/1.01  prop_fo_subsumed:                       68
% 3.65/1.01  prop_solver_time:                       0.
% 3.65/1.01  smt_solver_time:                        0.
% 3.65/1.01  smt_fast_solver_time:                   0.
% 3.65/1.01  prop_fast_solver_time:                  0.
% 3.65/1.01  prop_unsat_core_time:                   0.
% 3.65/1.01  
% 3.65/1.01  ------ QBF
% 3.65/1.01  
% 3.65/1.01  qbf_q_res:                              0
% 3.65/1.01  qbf_num_tautologies:                    0
% 3.65/1.01  qbf_prep_cycles:                        0
% 3.65/1.01  
% 3.65/1.01  ------ BMC1
% 3.65/1.01  
% 3.65/1.01  bmc1_current_bound:                     -1
% 3.65/1.01  bmc1_last_solved_bound:                 -1
% 3.65/1.01  bmc1_unsat_core_size:                   -1
% 3.65/1.01  bmc1_unsat_core_parents_size:           -1
% 3.65/1.01  bmc1_merge_next_fun:                    0
% 3.65/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.65/1.01  
% 3.65/1.01  ------ Instantiation
% 3.65/1.01  
% 3.65/1.01  inst_num_of_clauses:                    950
% 3.65/1.01  inst_num_in_passive:                    56
% 3.65/1.01  inst_num_in_active:                     429
% 3.65/1.01  inst_num_in_unprocessed:                464
% 3.65/1.01  inst_num_of_loops:                      568
% 3.65/1.01  inst_num_of_learning_restarts:          0
% 3.65/1.01  inst_num_moves_active_passive:          133
% 3.65/1.01  inst_lit_activity:                      0
% 3.65/1.01  inst_lit_activity_moves:                0
% 3.65/1.01  inst_num_tautologies:                   0
% 3.65/1.01  inst_num_prop_implied:                  0
% 3.65/1.01  inst_num_existing_simplified:           0
% 3.65/1.01  inst_num_eq_res_simplified:             0
% 3.65/1.01  inst_num_child_elim:                    0
% 3.65/1.01  inst_num_of_dismatching_blockings:      222
% 3.65/1.01  inst_num_of_non_proper_insts:           1028
% 3.65/1.01  inst_num_of_duplicates:                 0
% 3.65/1.01  inst_inst_num_from_inst_to_res:         0
% 3.65/1.01  inst_dismatching_checking_time:         0.
% 3.65/1.01  
% 3.65/1.01  ------ Resolution
% 3.65/1.01  
% 3.65/1.01  res_num_of_clauses:                     0
% 3.65/1.01  res_num_in_passive:                     0
% 3.65/1.01  res_num_in_active:                      0
% 3.65/1.01  res_num_of_loops:                       104
% 3.65/1.01  res_forward_subset_subsumed:            40
% 3.65/1.01  res_backward_subset_subsumed:           0
% 3.65/1.01  res_forward_subsumed:                   0
% 3.65/1.01  res_backward_subsumed:                  0
% 3.65/1.01  res_forward_subsumption_resolution:     3
% 3.65/1.01  res_backward_subsumption_resolution:    0
% 3.65/1.01  res_clause_to_clause_subsumption:       1213
% 3.65/1.01  res_orphan_elimination:                 0
% 3.65/1.01  res_tautology_del:                      48
% 3.65/1.01  res_num_eq_res_simplified:              0
% 3.65/1.01  res_num_sel_changes:                    0
% 3.65/1.01  res_moves_from_active_to_pass:          0
% 3.65/1.01  
% 3.65/1.01  ------ Superposition
% 3.65/1.01  
% 3.65/1.01  sup_time_total:                         0.
% 3.65/1.01  sup_time_generating:                    0.
% 3.65/1.01  sup_time_sim_full:                      0.
% 3.65/1.01  sup_time_sim_immed:                     0.
% 3.65/1.01  
% 3.65/1.01  sup_num_of_clauses:                     206
% 3.65/1.01  sup_num_in_active:                      26
% 3.65/1.01  sup_num_in_passive:                     180
% 3.65/1.01  sup_num_of_loops:                       112
% 3.65/1.01  sup_fw_superposition:                   182
% 3.65/1.01  sup_bw_superposition:                   334
% 3.65/1.01  sup_immediate_simplified:               104
% 3.65/1.01  sup_given_eliminated:                   12
% 3.65/1.01  comparisons_done:                       0
% 3.65/1.01  comparisons_avoided:                    20
% 3.65/1.01  
% 3.65/1.01  ------ Simplifications
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  sim_fw_subset_subsumed:                 41
% 3.65/1.01  sim_bw_subset_subsumed:                 121
% 3.65/1.01  sim_fw_subsumed:                        78
% 3.65/1.01  sim_bw_subsumed:                        61
% 3.65/1.01  sim_fw_subsumption_res:                 0
% 3.65/1.01  sim_bw_subsumption_res:                 0
% 3.65/1.01  sim_tautology_del:                      8
% 3.65/1.01  sim_eq_tautology_del:                   1
% 3.65/1.01  sim_eq_res_simp:                        0
% 3.65/1.01  sim_fw_demodulated:                     0
% 3.65/1.01  sim_bw_demodulated:                     48
% 3.65/1.01  sim_light_normalised:                   0
% 3.65/1.01  sim_joinable_taut:                      0
% 3.65/1.01  sim_joinable_simp:                      0
% 3.65/1.01  sim_ac_normalised:                      0
% 3.65/1.01  sim_smt_subsumption:                    0
% 3.65/1.01  
%------------------------------------------------------------------------------

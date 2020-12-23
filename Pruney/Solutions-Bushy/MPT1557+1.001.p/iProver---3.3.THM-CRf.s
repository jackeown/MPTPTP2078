%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1557+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:53 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 485 expanded)
%              Number of clauses        :   79 ( 153 expanded)
%              Number of leaves         :   12 ( 109 expanded)
%              Depth                    :   26
%              Number of atoms          :  492 (2264 expanded)
%              Number of equality atoms :  116 ( 177 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f13])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & r1_tarski(X1,X2) )
           => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
     => ( ~ r1_orders_2(X0,k2_yellow_0(X0,sK4),k2_yellow_0(X0,sK3))
        & r2_yellow_0(X0,sK4)
        & r2_yellow_0(X0,sK3)
        & r1_tarski(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,X2),k2_yellow_0(sK2,X1))
          & r2_yellow_0(sK2,X2)
          & r2_yellow_0(sK2,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    & r2_yellow_0(sK2,sK4)
    & r2_yellow_0(sK2,sK3)
    & r1_tarski(sK3,sK4)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34,f33])).

fof(f50,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f54,plain,(
    ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_488,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_489,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1528,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_225,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_1532,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1535,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2100,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1535])).

cnf(c_2374,plain,
    ( r1_lattice3(sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_2100])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1536,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3233,plain,
    ( r1_lattice3(sK2,sK3,X0) = iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2374,c_1536])).

cnf(c_9,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_443,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_444,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_1531,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1534,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2092,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1534])).

cnf(c_2367,plain,
    ( r1_lattice3(sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_2092])).

cnf(c_2610,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,X0)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_2367])).

cnf(c_16,negated_conjecture,
    ( r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_126,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_9])).

cnf(c_127,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_126])).

cnf(c_413,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_127,c_18])).

cnf(c_414,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_903,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_414])).

cnf(c_904,plain,
    ( ~ r1_lattice3(sK2,sK3,X0)
    | r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_1517,plain,
    ( r1_lattice3(sK2,sK3,X0) != iProver_top
    | r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK3)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_14,negated_conjecture,
    ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1533,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1773,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1533])).

cnf(c_992,plain,
    ( ~ r1_lattice3(sK2,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK3)
    | k2_yellow_0(sK2,sK4) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_904])).

cnf(c_993,plain,
    ( ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_999,plain,
    ( ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_993,c_444])).

cnf(c_1001,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_1796,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1773,c_1001])).

cnf(c_2649,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2610,c_1796])).

cnf(c_3238,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | r1_lattice3(sK2,sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3233,c_2649])).

cnf(c_3239,plain,
    ( r1_lattice3(sK2,sK3,X0) = iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3238])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_473,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_474,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1529,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_15,negated_conjecture,
    ( r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_119,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_9])).

cnf(c_431,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_119,c_18])).

cnf(c_432,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_820,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_432])).

cnf(c_821,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_1523,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_452,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_453,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_1530,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_2221,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),X0) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1530])).

cnf(c_2133,plain,
    ( m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_2134,plain,
    ( m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2133])).

cnf(c_2732,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_orders_2(sK2,k2_yellow_0(sK2,sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2221,c_2134])).

cnf(c_2733,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),X0) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2732])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_503,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_504,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1527,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,sK1(sK2,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_2742,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),sK4) != iProver_top
    | m1_subset_1(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_1527])).

cnf(c_2957,plain,
    ( m1_subset_1(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),sK4) != iProver_top
    | r1_lattice3(sK2,X0,k2_yellow_0(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_2134])).

cnf(c_2958,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),sK4) != iProver_top
    | m1_subset_1(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2957])).

cnf(c_2966,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),sK4) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_2958])).

cnf(c_2971,plain,
    ( r2_hidden(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),sK4) != iProver_top
    | r1_lattice3(sK2,X0,k2_yellow_0(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2966,c_2134])).

cnf(c_2972,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK1(sK2,X0,k2_yellow_0(sK2,sK4)),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2971])).

cnf(c_3247,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4)) = iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_2972])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3247,c_2134,c_1001])).


%------------------------------------------------------------------------------

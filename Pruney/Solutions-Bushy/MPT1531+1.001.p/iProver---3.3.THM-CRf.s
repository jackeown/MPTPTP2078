%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1531+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:47 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 630 expanded)
%              Number of clauses        :  106 ( 164 expanded)
%              Number of leaves         :   12 ( 191 expanded)
%              Depth                    :   13
%              Number of atoms          :  575 (3986 expanded)
%              Number of equality atoms :   85 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r2_lattice3(X0,X2,X3)
                   => r2_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                   => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ r2_lattice3(X0,X1,X3)
              & r2_lattice3(X0,X2,X3) )
            | ( ~ r1_lattice3(X0,X1,X3)
              & r1_lattice3(X0,X2,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ~ r2_lattice3(X0,X1,sK5)
            & r2_lattice3(X0,X2,sK5) )
          | ( ~ r1_lattice3(X0,X1,sK5)
            & r1_lattice3(X0,X2,sK5) ) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
     => ( ? [X3] :
            ( ( ( ~ r2_lattice3(X0,sK3,X3)
                & r2_lattice3(X0,sK4,X3) )
              | ( ~ r1_lattice3(X0,sK3,X3)
                & r1_lattice3(X0,sK4,X3) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_tarski(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(X0,X1,X3)
                    & r1_lattice3(X0,X2,X3) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK2,X1,X3)
                  & r2_lattice3(sK2,X2,X3) )
                | ( ~ r1_lattice3(sK2,X1,X3)
                  & r1_lattice3(sK2,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ( ~ r2_lattice3(sK2,sK3,sK5)
        & r2_lattice3(sK2,sK4,sK5) )
      | ( ~ r1_lattice3(sK2,sK3,sK5)
        & r1_lattice3(sK2,sK4,sK5) ) )
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & r1_tarski(sK3,sK4)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f31,f30,f29])).

fof(f45,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_227,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_18])).

cnf(c_2125,plain,
    ( ~ r2_lattice3(sK2,X0_45,X1_45)
    | r1_orders_2(sK2,X2_45,X1_45)
    | ~ r2_hidden(X2_45,X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_227])).

cnf(c_2654,plain,
    ( ~ r2_lattice3(sK2,sK4,X0_45)
    | r1_orders_2(sK2,sK1(sK2,sK3,sK5),X0_45)
    | ~ r2_hidden(sK1(sK2,sK3,sK5),sK4)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_2655,plain,
    ( r2_lattice3(sK2,sK4,X0_45) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,sK5),X0_45) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK4) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2654])).

cnf(c_2657,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK4) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2655])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2132,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X2_45))
    | ~ v1_xboole_0(X2_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2448,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_2517,plain,
    ( ~ r2_hidden(X0_45,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_2593,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_2594,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2593])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_289,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_18])).

cnf(c_2121,plain,
    ( r1_orders_2(sK2,X0_45,X1_45)
    | ~ r1_lattice3(sK2,X2_45,X0_45)
    | ~ r2_hidden(X1_45,X2_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_289])).

cnf(c_2554,plain,
    ( r1_orders_2(sK2,X0_45,sK0(sK2,sK3,sK5))
    | ~ r1_lattice3(sK2,sK4,X0_45)
    | ~ r2_hidden(sK0(sK2,sK3,sK5),sK4)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_2555,plain,
    ( r1_orders_2(sK2,X0_45,sK0(sK2,sK3,sK5)) = iProver_top
    | r1_lattice3(sK2,sK4,X0_45) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2554])).

cnf(c_2557,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_2522,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_2523,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2134,plain,
    ( r2_hidden(X0_45,X1_45)
    | ~ m1_subset_1(X0_45,X1_45)
    | v1_xboole_0(X1_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2403,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK4)
    | ~ m1_subset_1(sK1(sK2,sK3,sK5),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_2404,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK4) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2403])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2133,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | m1_subset_1(X0_45,X2_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X2_45)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2335,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | m1_subset_1(sK1(sK2,sK3,sK5),X0_45)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_45)) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_2379,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | m1_subset_1(sK1(sK2,sK3,sK5),sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2335])).

cnf(c_2380,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),sK4) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_2364,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_2365,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_2289,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | m1_subset_1(sK0(sK2,sK3,sK5),X0_45)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_45)) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_2340,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | m1_subset_1(sK0(sK2,sK3,sK5),sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_2341,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),sK4) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2340])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_323,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_18])).

cnf(c_2119,plain,
    ( r1_lattice3(sK2,X0_45,X1_45)
    | r2_hidden(sK0(sK2,X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_323])).

cnf(c_2243,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2119])).

cnf(c_2247,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2243])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_337,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_0,c_18])).

cnf(c_2118,plain,
    ( ~ r1_orders_2(sK2,X0_45,sK0(sK2,X1_45,X0_45))
    | r1_lattice3(sK2,X1_45,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_2240,plain,
    ( ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_2241,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_261,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_5,c_18])).

cnf(c_2123,plain,
    ( r2_lattice3(sK2,X0_45,X1_45)
    | r2_hidden(sK1(sK2,X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_2231,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_2232,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2231])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_275,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_4,c_18])).

cnf(c_2122,plain,
    ( r2_lattice3(sK2,X0_45,X1_45)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_45,X1_45),X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_275])).

cnf(c_2228,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2229,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2228])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_247,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_6,c_18])).

cnf(c_2124,plain,
    ( r2_lattice3(sK2,X0_45,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_45,X1_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_2225,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2124])).

cnf(c_2226,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2225])).

cnf(c_12,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_828,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_12,c_247])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_830,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_16])).

cnf(c_831,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_830])).

cnf(c_832,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_815,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_12,c_261])).

cnf(c_817,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_16])).

cnf(c_818,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
    inference(renaming,[status(thm)],[c_817])).

cnf(c_819,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_13,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_789,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_13,c_247])).

cnf(c_791,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_16])).

cnf(c_792,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_791])).

cnf(c_793,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_776,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_13,c_261])).

cnf(c_777,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_763,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
    | r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_13,c_275])).

cnf(c_764,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_549,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_12,c_337])).

cnf(c_550,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_14,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_536,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_14,c_337])).

cnf(c_537,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_309,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_523,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_12,c_309])).

cnf(c_525,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_16])).

cnf(c_526,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_525])).

cnf(c_527,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_510,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_12,c_323])).

cnf(c_511,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_497,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_14,c_309])).

cnf(c_499,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_16])).

cnf(c_500,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_501,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_484,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_14,c_323])).

cnf(c_485,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_200,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(resolution,[status(thm)],[c_9,c_17])).

cnf(c_201,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_15,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2657,c_2594,c_2557,c_2523,c_2404,c_2380,c_2365,c_2341,c_2247,c_2241,c_2232,c_2229,c_2226,c_832,c_819,c_793,c_777,c_764,c_550,c_537,c_527,c_511,c_501,c_485,c_201,c_22,c_21])).


%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:19:27 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 651 expanded)
%              Number of clauses        :   96 ( 155 expanded)
%              Number of leaves         :    9 ( 210 expanded)
%              Depth                    :   13
%              Number of atoms          :  502 (4271 expanded)
%              Number of equality atoms :   84 (  84 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f24,plain,
    ( ( ( ~ r2_lattice3(sK2,sK3,sK5)
        & r2_lattice3(sK2,sK4,sK5) )
      | ( ~ r1_lattice3(sK2,sK3,sK5)
        & r1_lattice3(sK2,sK4,sK5) ) )
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & r1_tarski(sK3,sK4)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f23,f22,f21])).

fof(f34,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f8,plain,(
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

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_178,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0) ),
    inference(resolution,[status(thm)],[c_8,c_15])).

cnf(c_1471,plain,
    ( ~ r2_lattice3(sK2,X0_44,X0_43)
    | r1_orders_2(sK2,X1_43,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK2))
    | ~ r2_hidden(X1_43,X0_44) ),
    inference(subtyping,[status(esa)],[c_178])).

cnf(c_1646,plain,
    ( ~ r2_lattice3(sK2,sK4,X0_43)
    | r1_orders_2(sK2,sK1(sK2,sK3,X1_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,sK3,X1_43),u1_struct_0(sK2))
    | ~ r2_hidden(sK1(sK2,sK3,X1_43),sK4) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_1652,plain,
    ( r2_lattice3(sK2,sK4,X0_43) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,X1_43),X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,X1_43),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X1_43),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_1654,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_164,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_0,c_14])).

cnf(c_1472,plain,
    ( r2_hidden(X0_43,sK4)
    | ~ r2_hidden(X0_43,sK3) ),
    inference(subtyping,[status(esa)],[c_164])).

cnf(c_1617,plain,
    ( r2_hidden(sK1(sK2,sK3,X0_43),sK4)
    | ~ r2_hidden(sK1(sK2,sK3,X0_43),sK3) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1620,plain,
    ( r2_hidden(sK1(sK2,sK3,X0_43),sK4) = iProver_top
    | r2_hidden(sK1(sK2,sK3,X0_43),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_1622,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK4) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_240,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X2) ),
    inference(resolution,[status(thm)],[c_4,c_15])).

cnf(c_1467,plain,
    ( r1_orders_2(sK2,X0_43,X1_43)
    | ~ r1_lattice3(sK2,X0_44,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK2))
    | ~ r2_hidden(X1_43,X0_44) ),
    inference(subtyping,[status(esa)],[c_240])).

cnf(c_1571,plain,
    ( r1_orders_2(sK2,X0_43,sK0(sK2,sK3,X1_43))
    | ~ r1_lattice3(sK2,sK4,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,X1_43),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK3,X1_43),sK4) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1572,plain,
    ( r1_orders_2(sK2,X0_43,sK0(sK2,sK3,X1_43)) = iProver_top
    | r1_lattice3(sK2,sK4,X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,X1_43),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,X1_43),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_1574,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_1553,plain,
    ( r2_hidden(sK0(sK2,sK3,X0_43),sK4)
    | ~ r2_hidden(sK0(sK2,sK3,X0_43),sK3) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1556,plain,
    ( r2_hidden(sK0(sK2,sK3,X0_43),sK4) = iProver_top
    | r2_hidden(sK0(sK2,sK3,X0_43),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1553])).

cnf(c_1558,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_288,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_15])).

cnf(c_1464,plain,
    ( ~ r1_orders_2(sK2,X0_43,sK0(sK2,X0_44,X0_43))
    | r1_lattice3(sK2,X0_44,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_1507,plain,
    ( r1_orders_2(sK2,X0_43,sK0(sK2,X0_44,X0_43)) != iProver_top
    | r1_lattice3(sK2,X0_44,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_1509,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_274,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_2,c_15])).

cnf(c_1465,plain,
    ( r1_lattice3(sK2,X0_44,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0_44,X0_43),X0_44) ),
    inference(subtyping,[status(esa)],[c_274])).

cnf(c_1504,plain,
    ( r1_lattice3(sK2,X0_44,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0_44,X0_43),X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_1506,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_3,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_260,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_15])).

cnf(c_1466,plain,
    ( r1_lattice3(sK2,X0_44,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_44,X0_43),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_260])).

cnf(c_1501,plain,
    ( r1_lattice3(sK2,X0_44,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_44,X0_43),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_1503,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_226,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_5,c_15])).

cnf(c_1468,plain,
    ( r2_lattice3(sK2,X0_44,X0_43)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_44,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_1495,plain,
    ( r2_lattice3(sK2,X0_44,X0_43) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_44,X0_43),X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_1497,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_7,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_198,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_15])).

cnf(c_1470,plain,
    ( r2_lattice3(sK2,X0_44,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_44,X0_43),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_1489,plain,
    ( r2_lattice3(sK2,X0_44,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_44,X0_43),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_1491,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_9,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_779,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_198])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_781,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_779,c_13])).

cnf(c_782,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_781])).

cnf(c_783,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_212,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK1(sK2,X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_6,c_15])).

cnf(c_766,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
    inference(resolution,[status(thm)],[c_9,c_212])).

cnf(c_768,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_766,c_13])).

cnf(c_770,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_753,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_226])).

cnf(c_755,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_13])).

cnf(c_756,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_757,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
    | r1_lattice3(sK2,sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_10,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_740,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

cnf(c_742,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_13])).

cnf(c_743,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_742])).

cnf(c_744,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_727,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
    inference(resolution,[status(thm)],[c_10,c_212])).

cnf(c_729,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_13])).

cnf(c_731,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_714,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
    | r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

cnf(c_716,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_13])).

cnf(c_717,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(renaming,[status(thm)],[c_716])).

cnf(c_718,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_11,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_487,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_288])).

cnf(c_488,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_474,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_260])).

cnf(c_476,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_13])).

cnf(c_477,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_478,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_461,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(resolution,[status(thm)],[c_9,c_274])).

cnf(c_463,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_13])).

cnf(c_465,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_448,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_260])).

cnf(c_450,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_13])).

cnf(c_451,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_452,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_435,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(resolution,[status(thm)],[c_11,c_274])).

cnf(c_437,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_13])).

cnf(c_439,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_12,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1654,c_1622,c_1574,c_1558,c_1509,c_1506,c_1503,c_1497,c_1491,c_783,c_770,c_757,c_744,c_731,c_718,c_488,c_478,c_465,c_452,c_439,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.83/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.83/0.98  
% 0.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/0.98  
% 0.83/0.98  ------  iProver source info
% 0.83/0.98  
% 0.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/0.98  git: non_committed_changes: false
% 0.83/0.98  git: last_make_outside_of_git: false
% 0.83/0.98  
% 0.83/0.98  ------ 
% 0.83/0.98  
% 0.83/0.98  ------ Input Options
% 0.83/0.98  
% 0.83/0.98  --out_options                           all
% 0.83/0.98  --tptp_safe_out                         true
% 0.83/0.98  --problem_path                          ""
% 0.83/0.98  --include_path                          ""
% 0.83/0.98  --clausifier                            res/vclausify_rel
% 0.83/0.98  --clausifier_options                    --mode clausify
% 0.83/0.98  --stdin                                 false
% 0.83/0.98  --stats_out                             all
% 0.83/0.98  
% 0.83/0.98  ------ General Options
% 0.83/0.98  
% 0.83/0.98  --fof                                   false
% 0.83/0.98  --time_out_real                         305.
% 0.83/0.98  --time_out_virtual                      -1.
% 0.83/0.98  --symbol_type_check                     false
% 0.83/0.98  --clausify_out                          false
% 0.83/0.98  --sig_cnt_out                           false
% 0.83/0.98  --trig_cnt_out                          false
% 0.83/0.98  --trig_cnt_out_tolerance                1.
% 0.83/0.98  --trig_cnt_out_sk_spl                   false
% 0.83/0.98  --abstr_cl_out                          false
% 0.83/0.98  
% 0.83/0.98  ------ Global Options
% 0.83/0.98  
% 0.83/0.98  --schedule                              default
% 0.83/0.98  --add_important_lit                     false
% 0.83/0.98  --prop_solver_per_cl                    1000
% 0.83/0.98  --min_unsat_core                        false
% 0.83/0.98  --soft_assumptions                      false
% 0.83/0.98  --soft_lemma_size                       3
% 0.83/0.98  --prop_impl_unit_size                   0
% 0.83/0.98  --prop_impl_unit                        []
% 0.83/0.98  --share_sel_clauses                     true
% 0.83/0.98  --reset_solvers                         false
% 0.83/0.98  --bc_imp_inh                            [conj_cone]
% 0.83/0.98  --conj_cone_tolerance                   3.
% 0.83/0.98  --extra_neg_conj                        none
% 0.83/0.98  --large_theory_mode                     true
% 0.83/0.98  --prolific_symb_bound                   200
% 0.83/0.98  --lt_threshold                          2000
% 0.83/0.98  --clause_weak_htbl                      true
% 0.83/0.98  --gc_record_bc_elim                     false
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing Options
% 0.83/0.98  
% 0.83/0.98  --preprocessing_flag                    true
% 0.83/0.98  --time_out_prep_mult                    0.1
% 0.83/0.98  --splitting_mode                        input
% 0.83/0.98  --splitting_grd                         true
% 0.83/0.98  --splitting_cvd                         false
% 0.83/0.98  --splitting_cvd_svl                     false
% 0.83/0.98  --splitting_nvd                         32
% 0.83/0.98  --sub_typing                            true
% 0.83/0.98  --prep_gs_sim                           true
% 0.83/0.98  --prep_unflatten                        true
% 0.83/0.98  --prep_res_sim                          true
% 0.83/0.98  --prep_upred                            true
% 0.83/0.98  --prep_sem_filter                       exhaustive
% 0.83/0.98  --prep_sem_filter_out                   false
% 0.83/0.98  --pred_elim                             true
% 0.83/0.98  --res_sim_input                         true
% 0.83/0.98  --eq_ax_congr_red                       true
% 0.83/0.98  --pure_diseq_elim                       true
% 0.83/0.98  --brand_transform                       false
% 0.83/0.98  --non_eq_to_eq                          false
% 0.83/0.98  --prep_def_merge                        true
% 0.83/0.98  --prep_def_merge_prop_impl              false
% 0.83/0.98  --prep_def_merge_mbd                    true
% 0.83/0.98  --prep_def_merge_tr_red                 false
% 0.83/0.98  --prep_def_merge_tr_cl                  false
% 0.83/0.98  --smt_preprocessing                     true
% 0.83/0.98  --smt_ac_axioms                         fast
% 0.83/0.98  --preprocessed_out                      false
% 0.83/0.98  --preprocessed_stats                    false
% 0.83/0.98  
% 0.83/0.98  ------ Abstraction refinement Options
% 0.83/0.98  
% 0.83/0.98  --abstr_ref                             []
% 0.83/0.98  --abstr_ref_prep                        false
% 0.83/0.98  --abstr_ref_until_sat                   false
% 0.83/0.98  --abstr_ref_sig_restrict                funpre
% 0.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.98  --abstr_ref_under                       []
% 0.83/0.98  
% 0.83/0.98  ------ SAT Options
% 0.83/0.98  
% 0.83/0.98  --sat_mode                              false
% 0.83/0.98  --sat_fm_restart_options                ""
% 0.83/0.98  --sat_gr_def                            false
% 0.83/0.98  --sat_epr_types                         true
% 0.83/0.98  --sat_non_cyclic_types                  false
% 0.83/0.98  --sat_finite_models                     false
% 0.83/0.98  --sat_fm_lemmas                         false
% 0.83/0.98  --sat_fm_prep                           false
% 0.83/0.98  --sat_fm_uc_incr                        true
% 0.83/0.98  --sat_out_model                         small
% 0.83/0.98  --sat_out_clauses                       false
% 0.83/0.98  
% 0.83/0.98  ------ QBF Options
% 0.83/0.98  
% 0.83/0.98  --qbf_mode                              false
% 0.83/0.98  --qbf_elim_univ                         false
% 0.83/0.98  --qbf_dom_inst                          none
% 0.83/0.98  --qbf_dom_pre_inst                      false
% 0.83/0.98  --qbf_sk_in                             false
% 0.83/0.98  --qbf_pred_elim                         true
% 0.83/0.98  --qbf_split                             512
% 0.83/0.98  
% 0.83/0.98  ------ BMC1 Options
% 0.83/0.98  
% 0.83/0.98  --bmc1_incremental                      false
% 0.83/0.98  --bmc1_axioms                           reachable_all
% 0.83/0.98  --bmc1_min_bound                        0
% 0.83/0.98  --bmc1_max_bound                        -1
% 0.83/0.98  --bmc1_max_bound_default                -1
% 0.83/0.98  --bmc1_symbol_reachability              true
% 0.83/0.98  --bmc1_property_lemmas                  false
% 0.83/0.98  --bmc1_k_induction                      false
% 0.83/0.98  --bmc1_non_equiv_states                 false
% 0.83/0.98  --bmc1_deadlock                         false
% 0.83/0.98  --bmc1_ucm                              false
% 0.83/0.98  --bmc1_add_unsat_core                   none
% 0.83/0.98  --bmc1_unsat_core_children              false
% 0.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.98  --bmc1_out_stat                         full
% 0.83/0.98  --bmc1_ground_init                      false
% 0.83/0.98  --bmc1_pre_inst_next_state              false
% 0.83/0.98  --bmc1_pre_inst_state                   false
% 0.83/0.98  --bmc1_pre_inst_reach_state             false
% 0.83/0.98  --bmc1_out_unsat_core                   false
% 0.83/0.98  --bmc1_aig_witness_out                  false
% 0.83/0.98  --bmc1_verbose                          false
% 0.83/0.98  --bmc1_dump_clauses_tptp                false
% 0.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.98  --bmc1_dump_file                        -
% 0.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.98  --bmc1_ucm_extend_mode                  1
% 0.83/0.98  --bmc1_ucm_init_mode                    2
% 0.83/0.98  --bmc1_ucm_cone_mode                    none
% 0.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.98  --bmc1_ucm_relax_model                  4
% 0.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.98  --bmc1_ucm_layered_model                none
% 0.83/0.98  --bmc1_ucm_max_lemma_size               10
% 0.83/0.98  
% 0.83/0.98  ------ AIG Options
% 0.83/0.98  
% 0.83/0.98  --aig_mode                              false
% 0.83/0.98  
% 0.83/0.98  ------ Instantiation Options
% 0.83/0.98  
% 0.83/0.98  --instantiation_flag                    true
% 0.83/0.98  --inst_sos_flag                         false
% 0.83/0.98  --inst_sos_phase                        true
% 0.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.98  --inst_lit_sel_side                     num_symb
% 0.83/0.98  --inst_solver_per_active                1400
% 0.83/0.98  --inst_solver_calls_frac                1.
% 0.83/0.98  --inst_passive_queue_type               priority_queues
% 0.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.98  --inst_passive_queues_freq              [25;2]
% 0.83/0.98  --inst_dismatching                      true
% 0.83/0.98  --inst_eager_unprocessed_to_passive     true
% 0.83/0.98  --inst_prop_sim_given                   true
% 0.83/0.98  --inst_prop_sim_new                     false
% 0.83/0.98  --inst_subs_new                         false
% 0.83/0.98  --inst_eq_res_simp                      false
% 0.83/0.98  --inst_subs_given                       false
% 0.83/0.98  --inst_orphan_elimination               true
% 0.83/0.98  --inst_learning_loop_flag               true
% 0.83/0.98  --inst_learning_start                   3000
% 0.83/0.98  --inst_learning_factor                  2
% 0.83/0.98  --inst_start_prop_sim_after_learn       3
% 0.83/0.98  --inst_sel_renew                        solver
% 0.83/0.98  --inst_lit_activity_flag                true
% 0.83/0.98  --inst_restr_to_given                   false
% 0.83/0.98  --inst_activity_threshold               500
% 0.83/0.98  --inst_out_proof                        true
% 0.83/0.98  
% 0.83/0.98  ------ Resolution Options
% 0.83/0.98  
% 0.83/0.98  --resolution_flag                       true
% 0.83/0.98  --res_lit_sel                           adaptive
% 0.83/0.98  --res_lit_sel_side                      none
% 0.83/0.98  --res_ordering                          kbo
% 0.83/0.98  --res_to_prop_solver                    active
% 0.83/0.98  --res_prop_simpl_new                    false
% 0.83/0.98  --res_prop_simpl_given                  true
% 0.83/0.98  --res_passive_queue_type                priority_queues
% 0.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.98  --res_passive_queues_freq               [15;5]
% 0.83/0.98  --res_forward_subs                      full
% 0.83/0.98  --res_backward_subs                     full
% 0.83/0.98  --res_forward_subs_resolution           true
% 0.83/0.98  --res_backward_subs_resolution          true
% 0.83/0.98  --res_orphan_elimination                true
% 0.83/0.98  --res_time_limit                        2.
% 0.83/0.98  --res_out_proof                         true
% 0.83/0.98  
% 0.83/0.98  ------ Superposition Options
% 0.83/0.98  
% 0.83/0.98  --superposition_flag                    true
% 0.83/0.98  --sup_passive_queue_type                priority_queues
% 0.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.98  --demod_completeness_check              fast
% 0.83/0.98  --demod_use_ground                      true
% 0.83/0.98  --sup_to_prop_solver                    passive
% 0.83/0.98  --sup_prop_simpl_new                    true
% 0.83/0.98  --sup_prop_simpl_given                  true
% 0.83/0.98  --sup_fun_splitting                     false
% 0.83/0.98  --sup_smt_interval                      50000
% 0.83/0.98  
% 0.83/0.98  ------ Superposition Simplification Setup
% 0.83/0.98  
% 0.83/0.98  --sup_indices_passive                   []
% 0.83/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_full_bw                           [BwDemod]
% 0.83/0.98  --sup_immed_triv                        [TrivRules]
% 0.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_immed_bw_main                     []
% 0.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.98  
% 0.83/0.98  ------ Combination Options
% 0.83/0.98  
% 0.83/0.98  --comb_res_mult                         3
% 0.83/0.98  --comb_sup_mult                         2
% 0.83/0.98  --comb_inst_mult                        10
% 0.83/0.98  
% 0.83/0.98  ------ Debug Options
% 0.83/0.98  
% 0.83/0.98  --dbg_backtrace                         false
% 0.83/0.98  --dbg_dump_prop_clauses                 false
% 0.83/0.98  --dbg_dump_prop_clauses_file            -
% 0.83/0.98  --dbg_out_stat                          false
% 0.83/0.98  ------ Parsing...
% 0.83/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/0.98  ------ Proving...
% 0.83/0.98  ------ Problem Properties 
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  clauses                                 14
% 0.83/0.98  conjectures                             5
% 0.83/0.98  EPR                                     5
% 0.83/0.98  Horn                                    9
% 0.83/0.98  unary                                   1
% 0.83/0.98  binary                                  5
% 0.83/0.98  lits                                    39
% 0.83/0.98  lits eq                                 0
% 0.83/0.98  fd_pure                                 0
% 0.83/0.98  fd_pseudo                               0
% 0.83/0.98  fd_cond                                 0
% 0.83/0.98  fd_pseudo_cond                          0
% 0.83/0.98  AC symbols                              0
% 0.83/0.98  
% 0.83/0.98  ------ Schedule dynamic 5 is on 
% 0.83/0.98  
% 0.83/0.98  ------ no equalities: superposition off 
% 0.83/0.98  
% 0.83/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  ------ 
% 0.83/0.98  Current options:
% 0.83/0.98  ------ 
% 0.83/0.98  
% 0.83/0.98  ------ Input Options
% 0.83/0.98  
% 0.83/0.98  --out_options                           all
% 0.83/0.98  --tptp_safe_out                         true
% 0.83/0.98  --problem_path                          ""
% 0.83/0.98  --include_path                          ""
% 0.83/0.98  --clausifier                            res/vclausify_rel
% 0.83/0.98  --clausifier_options                    --mode clausify
% 0.83/0.98  --stdin                                 false
% 0.83/0.98  --stats_out                             all
% 0.83/0.98  
% 0.83/0.98  ------ General Options
% 0.83/0.98  
% 0.83/0.98  --fof                                   false
% 0.83/0.98  --time_out_real                         305.
% 0.83/0.98  --time_out_virtual                      -1.
% 0.83/0.98  --symbol_type_check                     false
% 0.83/0.98  --clausify_out                          false
% 0.83/0.98  --sig_cnt_out                           false
% 0.83/0.98  --trig_cnt_out                          false
% 0.83/0.98  --trig_cnt_out_tolerance                1.
% 0.83/0.98  --trig_cnt_out_sk_spl                   false
% 0.83/0.98  --abstr_cl_out                          false
% 0.83/0.98  
% 0.83/0.98  ------ Global Options
% 0.83/0.98  
% 0.83/0.98  --schedule                              default
% 0.83/0.98  --add_important_lit                     false
% 0.83/0.98  --prop_solver_per_cl                    1000
% 0.83/0.98  --min_unsat_core                        false
% 0.83/0.98  --soft_assumptions                      false
% 0.83/0.98  --soft_lemma_size                       3
% 0.83/0.98  --prop_impl_unit_size                   0
% 0.83/0.98  --prop_impl_unit                        []
% 0.83/0.98  --share_sel_clauses                     true
% 0.83/0.98  --reset_solvers                         false
% 0.83/0.98  --bc_imp_inh                            [conj_cone]
% 0.83/0.98  --conj_cone_tolerance                   3.
% 0.83/0.98  --extra_neg_conj                        none
% 0.83/0.98  --large_theory_mode                     true
% 0.83/0.98  --prolific_symb_bound                   200
% 0.83/0.98  --lt_threshold                          2000
% 0.83/0.98  --clause_weak_htbl                      true
% 0.83/0.98  --gc_record_bc_elim                     false
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing Options
% 0.83/0.98  
% 0.83/0.98  --preprocessing_flag                    true
% 0.83/0.98  --time_out_prep_mult                    0.1
% 0.83/0.98  --splitting_mode                        input
% 0.83/0.98  --splitting_grd                         true
% 0.83/0.98  --splitting_cvd                         false
% 0.83/0.98  --splitting_cvd_svl                     false
% 0.83/0.98  --splitting_nvd                         32
% 0.83/0.98  --sub_typing                            true
% 0.83/0.98  --prep_gs_sim                           true
% 0.83/0.98  --prep_unflatten                        true
% 0.83/0.98  --prep_res_sim                          true
% 0.83/0.98  --prep_upred                            true
% 0.83/0.98  --prep_sem_filter                       exhaustive
% 0.83/0.98  --prep_sem_filter_out                   false
% 0.83/0.98  --pred_elim                             true
% 0.83/0.98  --res_sim_input                         true
% 0.83/0.98  --eq_ax_congr_red                       true
% 0.83/0.98  --pure_diseq_elim                       true
% 0.83/0.98  --brand_transform                       false
% 0.83/0.98  --non_eq_to_eq                          false
% 0.83/0.98  --prep_def_merge                        true
% 0.83/0.98  --prep_def_merge_prop_impl              false
% 0.83/0.98  --prep_def_merge_mbd                    true
% 0.83/0.98  --prep_def_merge_tr_red                 false
% 0.83/0.98  --prep_def_merge_tr_cl                  false
% 0.83/0.98  --smt_preprocessing                     true
% 0.83/0.98  --smt_ac_axioms                         fast
% 0.83/0.98  --preprocessed_out                      false
% 0.83/0.98  --preprocessed_stats                    false
% 0.83/0.98  
% 0.83/0.98  ------ Abstraction refinement Options
% 0.83/0.98  
% 0.83/0.98  --abstr_ref                             []
% 0.83/0.98  --abstr_ref_prep                        false
% 0.83/0.98  --abstr_ref_until_sat                   false
% 0.83/0.98  --abstr_ref_sig_restrict                funpre
% 0.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.98  --abstr_ref_under                       []
% 0.83/0.98  
% 0.83/0.98  ------ SAT Options
% 0.83/0.98  
% 0.83/0.98  --sat_mode                              false
% 0.83/0.98  --sat_fm_restart_options                ""
% 0.83/0.98  --sat_gr_def                            false
% 0.83/0.98  --sat_epr_types                         true
% 0.83/0.98  --sat_non_cyclic_types                  false
% 0.83/0.98  --sat_finite_models                     false
% 0.83/0.98  --sat_fm_lemmas                         false
% 0.83/0.98  --sat_fm_prep                           false
% 0.83/0.98  --sat_fm_uc_incr                        true
% 0.83/0.98  --sat_out_model                         small
% 0.83/0.98  --sat_out_clauses                       false
% 0.83/0.98  
% 0.83/0.98  ------ QBF Options
% 0.83/0.98  
% 0.83/0.98  --qbf_mode                              false
% 0.83/0.98  --qbf_elim_univ                         false
% 0.83/0.98  --qbf_dom_inst                          none
% 0.83/0.98  --qbf_dom_pre_inst                      false
% 0.83/0.98  --qbf_sk_in                             false
% 0.83/0.98  --qbf_pred_elim                         true
% 0.83/0.98  --qbf_split                             512
% 0.83/0.98  
% 0.83/0.98  ------ BMC1 Options
% 0.83/0.98  
% 0.83/0.98  --bmc1_incremental                      false
% 0.83/0.98  --bmc1_axioms                           reachable_all
% 0.83/0.98  --bmc1_min_bound                        0
% 0.83/0.98  --bmc1_max_bound                        -1
% 0.83/0.98  --bmc1_max_bound_default                -1
% 0.83/0.98  --bmc1_symbol_reachability              true
% 0.83/0.98  --bmc1_property_lemmas                  false
% 0.83/0.98  --bmc1_k_induction                      false
% 0.83/0.98  --bmc1_non_equiv_states                 false
% 0.83/0.98  --bmc1_deadlock                         false
% 0.83/0.98  --bmc1_ucm                              false
% 0.83/0.98  --bmc1_add_unsat_core                   none
% 0.83/0.98  --bmc1_unsat_core_children              false
% 0.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.98  --bmc1_out_stat                         full
% 0.83/0.98  --bmc1_ground_init                      false
% 0.83/0.98  --bmc1_pre_inst_next_state              false
% 0.83/0.98  --bmc1_pre_inst_state                   false
% 0.83/0.98  --bmc1_pre_inst_reach_state             false
% 0.83/0.98  --bmc1_out_unsat_core                   false
% 0.83/0.98  --bmc1_aig_witness_out                  false
% 0.83/0.98  --bmc1_verbose                          false
% 0.83/0.98  --bmc1_dump_clauses_tptp                false
% 0.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.98  --bmc1_dump_file                        -
% 0.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.98  --bmc1_ucm_extend_mode                  1
% 0.83/0.98  --bmc1_ucm_init_mode                    2
% 0.83/0.98  --bmc1_ucm_cone_mode                    none
% 0.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.98  --bmc1_ucm_relax_model                  4
% 0.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.98  --bmc1_ucm_layered_model                none
% 0.83/0.98  --bmc1_ucm_max_lemma_size               10
% 0.83/0.98  
% 0.83/0.98  ------ AIG Options
% 0.83/0.98  
% 0.83/0.98  --aig_mode                              false
% 0.83/0.98  
% 0.83/0.98  ------ Instantiation Options
% 0.83/0.98  
% 0.83/0.98  --instantiation_flag                    true
% 0.83/0.98  --inst_sos_flag                         false
% 0.83/0.98  --inst_sos_phase                        true
% 0.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.98  --inst_lit_sel_side                     none
% 0.83/0.98  --inst_solver_per_active                1400
% 0.83/0.98  --inst_solver_calls_frac                1.
% 0.83/0.98  --inst_passive_queue_type               priority_queues
% 0.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.98  --inst_passive_queues_freq              [25;2]
% 0.83/0.98  --inst_dismatching                      true
% 0.83/0.98  --inst_eager_unprocessed_to_passive     true
% 0.83/0.98  --inst_prop_sim_given                   true
% 0.83/0.98  --inst_prop_sim_new                     false
% 0.83/0.98  --inst_subs_new                         false
% 0.83/0.98  --inst_eq_res_simp                      false
% 0.83/0.98  --inst_subs_given                       false
% 0.83/0.98  --inst_orphan_elimination               true
% 0.83/0.98  --inst_learning_loop_flag               true
% 0.83/0.98  --inst_learning_start                   3000
% 0.83/0.98  --inst_learning_factor                  2
% 0.83/0.98  --inst_start_prop_sim_after_learn       3
% 0.83/0.98  --inst_sel_renew                        solver
% 0.83/0.98  --inst_lit_activity_flag                true
% 0.83/0.98  --inst_restr_to_given                   false
% 0.83/0.98  --inst_activity_threshold               500
% 0.83/0.98  --inst_out_proof                        true
% 0.83/0.98  
% 0.83/0.98  ------ Resolution Options
% 0.83/0.98  
% 0.83/0.98  --resolution_flag                       false
% 0.83/0.98  --res_lit_sel                           adaptive
% 0.83/0.98  --res_lit_sel_side                      none
% 0.83/0.98  --res_ordering                          kbo
% 0.83/0.98  --res_to_prop_solver                    active
% 0.83/0.98  --res_prop_simpl_new                    false
% 0.83/0.98  --res_prop_simpl_given                  true
% 0.83/0.98  --res_passive_queue_type                priority_queues
% 0.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.98  --res_passive_queues_freq               [15;5]
% 0.83/0.98  --res_forward_subs                      full
% 0.83/0.98  --res_backward_subs                     full
% 0.83/0.98  --res_forward_subs_resolution           true
% 0.83/0.98  --res_backward_subs_resolution          true
% 0.83/0.98  --res_orphan_elimination                true
% 0.83/0.98  --res_time_limit                        2.
% 0.83/0.98  --res_out_proof                         true
% 0.83/0.98  
% 0.83/0.98  ------ Superposition Options
% 0.83/0.98  
% 0.83/0.98  --superposition_flag                    false
% 0.83/0.98  --sup_passive_queue_type                priority_queues
% 0.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.98  --demod_completeness_check              fast
% 0.83/0.98  --demod_use_ground                      true
% 0.83/0.98  --sup_to_prop_solver                    passive
% 0.83/0.98  --sup_prop_simpl_new                    true
% 0.83/0.98  --sup_prop_simpl_given                  true
% 0.83/0.98  --sup_fun_splitting                     false
% 0.83/0.98  --sup_smt_interval                      50000
% 0.83/0.98  
% 0.83/0.98  ------ Superposition Simplification Setup
% 0.83/0.98  
% 0.83/0.98  --sup_indices_passive                   []
% 0.83/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_full_bw                           [BwDemod]
% 0.83/0.98  --sup_immed_triv                        [TrivRules]
% 0.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_immed_bw_main                     []
% 0.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.98  
% 0.83/0.98  ------ Combination Options
% 0.83/0.98  
% 0.83/0.98  --comb_res_mult                         3
% 0.83/0.98  --comb_sup_mult                         2
% 0.83/0.98  --comb_inst_mult                        10
% 0.83/0.98  
% 0.83/0.98  ------ Debug Options
% 0.83/0.98  
% 0.83/0.98  --dbg_backtrace                         false
% 0.83/0.98  --dbg_dump_prop_clauses                 false
% 0.83/0.98  --dbg_dump_prop_clauses_file            -
% 0.83/0.98  --dbg_out_stat                          false
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  ------ Proving...
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  % SZS status Theorem for theBenchmark.p
% 0.83/0.98  
% 0.83/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/0.98  
% 0.83/0.98  fof(f3,axiom,(
% 0.83/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.83/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/0.98  
% 0.83/0.98  fof(f10,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(ennf_transformation,[],[f3])).
% 0.83/0.98  
% 0.83/0.98  fof(f11,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(flattening,[],[f10])).
% 0.83/0.98  
% 0.83/0.98  fof(f17,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(nnf_transformation,[],[f11])).
% 0.83/0.98  
% 0.83/0.98  fof(f18,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(rectify,[],[f17])).
% 0.83/0.98  
% 0.83/0.98  fof(f19,plain,(
% 0.83/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.83/0.98    introduced(choice_axiom,[])).
% 0.83/0.98  
% 0.83/0.98  fof(f20,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 0.83/0.98  
% 0.83/0.98  fof(f30,plain,(
% 0.83/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f20])).
% 0.83/0.98  
% 0.83/0.98  fof(f4,conjecture,(
% 0.83/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.83/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/0.98  
% 0.83/0.98  fof(f5,negated_conjecture,(
% 0.83/0.98    ~! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.83/0.98    inference(negated_conjecture,[],[f4])).
% 0.83/0.98  
% 0.83/0.98  fof(f12,plain,(
% 0.83/0.98    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0))),
% 0.83/0.98    inference(ennf_transformation,[],[f5])).
% 0.83/0.98  
% 0.83/0.98  fof(f23,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) => (((~r2_lattice3(X0,X1,sK5) & r2_lattice3(X0,X2,sK5)) | (~r1_lattice3(X0,X1,sK5) & r1_lattice3(X0,X2,sK5))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 0.83/0.98    introduced(choice_axiom,[])).
% 0.83/0.98  
% 0.83/0.98  fof(f22,plain,(
% 0.83/0.98    ( ! [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) => (? [X3] : (((~r2_lattice3(X0,sK3,X3) & r2_lattice3(X0,sK4,X3)) | (~r1_lattice3(X0,sK3,X3) & r1_lattice3(X0,sK4,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(sK3,sK4))) )),
% 0.83/0.98    introduced(choice_axiom,[])).
% 0.83/0.98  
% 0.83/0.98  fof(f21,plain,(
% 0.83/0.98    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0)) => (? [X2,X1] : (? [X3] : (((~r2_lattice3(sK2,X1,X3) & r2_lattice3(sK2,X2,X3)) | (~r1_lattice3(sK2,X1,X3) & r1_lattice3(sK2,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_tarski(X1,X2)) & l1_orders_2(sK2))),
% 0.83/0.98    introduced(choice_axiom,[])).
% 0.83/0.98  
% 0.83/0.98  fof(f24,plain,(
% 0.83/0.98    ((((~r2_lattice3(sK2,sK3,sK5) & r2_lattice3(sK2,sK4,sK5)) | (~r1_lattice3(sK2,sK3,sK5) & r1_lattice3(sK2,sK4,sK5))) & m1_subset_1(sK5,u1_struct_0(sK2))) & r1_tarski(sK3,sK4)) & l1_orders_2(sK2)),
% 0.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f23,f22,f21])).
% 0.83/0.98  
% 0.83/0.98  fof(f34,plain,(
% 0.83/0.98    l1_orders_2(sK2)),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  fof(f1,axiom,(
% 0.83/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.83/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/0.98  
% 0.83/0.98  fof(f6,plain,(
% 0.83/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.83/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 0.83/0.98  
% 0.83/0.98  fof(f7,plain,(
% 0.83/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.83/0.98    inference(ennf_transformation,[],[f6])).
% 0.83/0.98  
% 0.83/0.98  fof(f25,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f7])).
% 0.83/0.98  
% 0.83/0.98  fof(f35,plain,(
% 0.83/0.98    r1_tarski(sK3,sK4)),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  fof(f2,axiom,(
% 0.83/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.83/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/0.98  
% 0.83/0.98  fof(f8,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(ennf_transformation,[],[f2])).
% 0.83/0.98  
% 0.83/0.98  fof(f9,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(flattening,[],[f8])).
% 0.83/0.98  
% 0.83/0.98  fof(f13,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(nnf_transformation,[],[f9])).
% 0.83/0.98  
% 0.83/0.98  fof(f14,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(rectify,[],[f13])).
% 0.83/0.98  
% 0.83/0.98  fof(f15,plain,(
% 0.83/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 0.83/0.98    introduced(choice_axiom,[])).
% 0.83/0.98  
% 0.83/0.98  fof(f16,plain,(
% 0.83/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 0.83/0.98  
% 0.83/0.98  fof(f26,plain,(
% 0.83/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f16])).
% 0.83/0.98  
% 0.83/0.98  fof(f29,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f16])).
% 0.83/0.98  
% 0.83/0.98  fof(f28,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f16])).
% 0.83/0.98  
% 0.83/0.98  fof(f27,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f16])).
% 0.83/0.98  
% 0.83/0.98  fof(f33,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f20])).
% 0.83/0.98  
% 0.83/0.98  fof(f31,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f20])).
% 0.83/0.98  
% 0.83/0.98  fof(f40,plain,(
% 0.83/0.98    ~r2_lattice3(sK2,sK3,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  fof(f36,plain,(
% 0.83/0.98    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  fof(f32,plain,(
% 0.83/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.83/0.98    inference(cnf_transformation,[],[f20])).
% 0.83/0.98  
% 0.83/0.98  fof(f39,plain,(
% 0.83/0.98    ~r2_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5)),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  fof(f38,plain,(
% 0.83/0.98    r2_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  fof(f37,plain,(
% 0.83/0.98    r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5)),
% 0.83/0.98    inference(cnf_transformation,[],[f24])).
% 0.83/0.98  
% 0.83/0.98  cnf(c_8,plain,
% 0.83/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 0.83/0.98      | r1_orders_2(X0,X3,X2)
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.83/0.98      | ~ r2_hidden(X3,X1)
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f30]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_15,negated_conjecture,
% 0.83/0.98      ( l1_orders_2(sK2) ),
% 0.83/0.98      inference(cnf_transformation,[],[f34]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_178,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,X0,X1)
% 0.83/0.98      | r1_orders_2(sK2,X2,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_hidden(X2,X0) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_8,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1471,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | r1_orders_2(sK2,X1_43,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(X1_43,u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_hidden(X1_43,X0_44) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_178]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1646,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK4,X0_43)
% 0.83/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,X1_43),X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(sK1(sK2,sK3,X1_43),u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_hidden(sK1(sK2,sK3,X1_43),sK4) ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1471]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1652,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,X0_43) != iProver_top
% 0.83/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,X1_43),X0_43) = iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,X1_43),u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,X1_43),sK4) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1654,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) != iProver_top
% 0.83/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,sK5),sK4) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1652]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_0,plain,
% 0.83/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 0.83/0.98      inference(cnf_transformation,[],[f25]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_14,negated_conjecture,
% 0.83/0.98      ( r1_tarski(sK3,sK4) ),
% 0.83/0.98      inference(cnf_transformation,[],[f35]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_164,plain,
% 0.83/0.98      ( r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK3) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_0,c_14]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1472,plain,
% 0.83/0.98      ( r2_hidden(X0_43,sK4) | ~ r2_hidden(X0_43,sK3) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_164]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1617,plain,
% 0.83/0.98      ( r2_hidden(sK1(sK2,sK3,X0_43),sK4)
% 0.83/0.98      | ~ r2_hidden(sK1(sK2,sK3,X0_43),sK3) ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1472]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1620,plain,
% 0.83/0.98      ( r2_hidden(sK1(sK2,sK3,X0_43),sK4) = iProver_top
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,X0_43),sK3) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1622,plain,
% 0.83/0.98      ( r2_hidden(sK1(sK2,sK3,sK5),sK4) = iProver_top
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,sK5),sK3) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1620]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_4,plain,
% 0.83/0.98      ( r1_orders_2(X0,X1,X2)
% 0.83/0.98      | ~ r1_lattice3(X0,X3,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | ~ r2_hidden(X2,X3)
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f26]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_240,plain,
% 0.83/0.98      ( r1_orders_2(sK2,X0,X1)
% 0.83/0.98      | ~ r1_lattice3(sK2,X2,X0)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_hidden(X1,X2) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_4,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1467,plain,
% 0.83/0.98      ( r1_orders_2(sK2,X0_43,X1_43)
% 0.83/0.98      | ~ r1_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(X1_43,u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_hidden(X1_43,X0_44) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_240]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1571,plain,
% 0.83/0.98      ( r1_orders_2(sK2,X0_43,sK0(sK2,sK3,X1_43))
% 0.83/0.98      | ~ r1_lattice3(sK2,sK4,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(sK0(sK2,sK3,X1_43),u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_hidden(sK0(sK2,sK3,X1_43),sK4) ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1467]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1572,plain,
% 0.83/0.98      ( r1_orders_2(sK2,X0_43,sK0(sK2,sK3,X1_43)) = iProver_top
% 0.83/0.98      | r1_lattice3(sK2,sK4,X0_43) != iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,X1_43),u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,X1_43),sK4) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1574,plain,
% 0.83/0.98      ( r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
% 0.83/0.98      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1572]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1553,plain,
% 0.83/0.98      ( r2_hidden(sK0(sK2,sK3,X0_43),sK4)
% 0.83/0.98      | ~ r2_hidden(sK0(sK2,sK3,X0_43),sK3) ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1472]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1556,plain,
% 0.83/0.98      ( r2_hidden(sK0(sK2,sK3,X0_43),sK4) = iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,X0_43),sK3) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1553]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1558,plain,
% 0.83/0.98      ( r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1556]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1,plain,
% 0.83/0.98      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 0.83/0.98      | r1_lattice3(X0,X2,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f29]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_288,plain,
% 0.83/0.98      ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
% 0.83/0.98      | r1_lattice3(sK2,X1,X0)
% 0.83/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_1,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1464,plain,
% 0.83/0.98      ( ~ r1_orders_2(sK2,X0_43,sK0(sK2,X0_44,X0_43))
% 0.83/0.98      | r1_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_288]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1507,plain,
% 0.83/0.98      ( r1_orders_2(sK2,X0_43,sK0(sK2,X0_44,X0_43)) != iProver_top
% 0.83/0.98      | r1_lattice3(sK2,X0_44,X0_43) = iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1509,plain,
% 0.83/0.98      ( r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
% 0.83/0.98      | r1_lattice3(sK2,sK3,sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1507]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_2,plain,
% 0.83/0.98      ( r1_lattice3(X0,X1,X2)
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f28]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_274,plain,
% 0.83/0.98      ( r1_lattice3(sK2,X0,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_2,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1465,plain,
% 0.83/0.98      ( r1_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK0(sK2,X0_44,X0_43),X0_44) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_274]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1504,plain,
% 0.83/0.98      ( r1_lattice3(sK2,X0_44,X0_43) = iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,X0_44,X0_43),X0_44) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1506,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1504]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_3,plain,
% 0.83/0.98      ( r1_lattice3(X0,X1,X2)
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f27]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_260,plain,
% 0.83/0.98      ( r1_lattice3(sK2,X0,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.83/0.98      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_3,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1466,plain,
% 0.83/0.98      ( r1_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | m1_subset_1(sK0(sK2,X0_44,X0_43),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_260]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1501,plain,
% 0.83/0.98      ( r1_lattice3(sK2,X0_44,X0_43) = iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK0(sK2,X0_44,X0_43),u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1503,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1501]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_5,plain,
% 0.83/0.98      ( r2_lattice3(X0,X1,X2)
% 0.83/0.98      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f33]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_226,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0,X1)
% 0.83/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_5,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1468,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X0_44,X0_43),X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_226]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1495,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0_44,X0_43) = iProver_top
% 0.83/0.98      | r1_orders_2(sK2,sK1(sK2,X0_44,X0_43),X0_43) != iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1497,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 0.83/0.98      | r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1495]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_7,plain,
% 0.83/0.98      ( r2_lattice3(X0,X1,X2)
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f31]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_198,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.83/0.98      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_7,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1470,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0_44,X0_43)
% 0.83/0.98      | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
% 0.83/0.98      | m1_subset_1(sK1(sK2,X0_44,X0_43),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(subtyping,[status(esa)],[c_198]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1489,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0_44,X0_43) = iProver_top
% 0.83/0.98      | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK1(sK2,X0_44,X0_43),u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_1491,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(instantiation,[status(thm)],[c_1489]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_9,negated_conjecture,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK3,sK5) ),
% 0.83/0.98      inference(cnf_transformation,[],[f40]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_779,plain,
% 0.83/0.98      ( ~ r1_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_9,c_198]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_13,negated_conjecture,
% 0.83/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(cnf_transformation,[],[f36]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_781,plain,
% 0.83/0.98      ( m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | ~ r1_lattice3(sK2,sK3,sK5) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_779,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_782,plain,
% 0.83/0.98      ( ~ r1_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(renaming,[status(thm)],[c_781]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_783,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_6,plain,
% 0.83/0.98      ( r2_lattice3(X0,X1,X2)
% 0.83/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.83/0.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 0.83/0.98      | ~ l1_orders_2(X0) ),
% 0.83/0.98      inference(cnf_transformation,[],[f32]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_212,plain,
% 0.83/0.98      ( r2_lattice3(sK2,X0,X1)
% 0.83/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK1(sK2,X0,X1),X0) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_6,c_15]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_766,plain,
% 0.83/0.98      ( ~ r1_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_9,c_212]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_768,plain,
% 0.83/0.98      ( ~ r1_lattice3(sK2,sK3,sK5) | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_766,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_770,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_753,plain,
% 0.83/0.98      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
% 0.83/0.98      | ~ r1_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_9,c_226]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_755,plain,
% 0.83/0.98      ( ~ r1_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_753,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_756,plain,
% 0.83/0.98      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
% 0.83/0.98      | ~ r1_lattice3(sK2,sK3,sK5) ),
% 0.83/0.98      inference(renaming,[status(thm)],[c_755]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_757,plain,
% 0.83/0.98      ( r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
% 0.83/0.98      | r1_lattice3(sK2,sK3,sK5) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_10,negated_conjecture,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 0.83/0.98      inference(cnf_transformation,[],[f39]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_740,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_10,c_198]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_742,plain,
% 0.83/0.98      ( m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | r1_lattice3(sK2,sK4,sK5) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_740,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_743,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(renaming,[status(thm)],[c_742]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_744,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK1(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_727,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_10,c_212]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_729,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5) | r2_hidden(sK1(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_727,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_731,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 0.83/0.98      | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_714,plain,
% 0.83/0.98      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
% 0.83/0.98      | r1_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_10,c_226]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_716,plain,
% 0.83/0.98      ( r1_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_714,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_717,plain,
% 0.83/0.98      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5)
% 0.83/0.98      | r1_lattice3(sK2,sK4,sK5) ),
% 0.83/0.98      inference(renaming,[status(thm)],[c_716]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_718,plain,
% 0.83/0.98      ( r1_orders_2(sK2,sK1(sK2,sK3,sK5),sK5) != iProver_top
% 0.83/0.98      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_11,negated_conjecture,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) | ~ r1_lattice3(sK2,sK3,sK5) ),
% 0.83/0.98      inference(cnf_transformation,[],[f38]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_487,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_11,c_288]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_488,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 0.83/0.98      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
% 0.83/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_474,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_9,c_260]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_476,plain,
% 0.83/0.98      ( m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | ~ r2_lattice3(sK2,sK3,sK5) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_474,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_477,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(renaming,[status(thm)],[c_476]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_478,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_461,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK3,sK5)
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_9,c_274]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_463,plain,
% 0.83/0.98      ( ~ r2_lattice3(sK2,sK3,sK5) | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_461,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_465,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_448,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_11,c_260]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_450,plain,
% 0.83/0.98      ( m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 0.83/0.98      | r2_lattice3(sK2,sK4,sK5) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_448,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_451,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 0.83/0.98      inference(renaming,[status(thm)],[c_450]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_452,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 0.83/0.98      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_435,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5)
% 0.83/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(resolution,[status(thm)],[c_11,c_274]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_437,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 0.83/0.98      inference(global_propositional_subsumption,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_435,c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_439,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 0.83/0.98      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_12,negated_conjecture,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 0.83/0.98      inference(cnf_transformation,[],[f37]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_19,plain,
% 0.83/0.98      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 0.83/0.98      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(c_18,plain,
% 0.83/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 0.83/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.83/0.98  
% 0.83/0.98  cnf(contradiction,plain,
% 0.83/0.98      ( $false ),
% 0.83/0.98      inference(minisat,
% 0.83/0.98                [status(thm)],
% 0.83/0.98                [c_1654,c_1622,c_1574,c_1558,c_1509,c_1506,c_1503,c_1497,
% 0.83/0.98                 c_1491,c_783,c_770,c_757,c_744,c_731,c_718,c_488,c_478,
% 0.83/0.98                 c_465,c_452,c_439,c_19,c_18]) ).
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/0.98  
% 0.83/0.98  ------                               Statistics
% 0.83/0.98  
% 0.83/0.98  ------ General
% 0.83/0.98  
% 0.83/0.98  abstr_ref_over_cycles:                  0
% 0.83/0.98  abstr_ref_under_cycles:                 0
% 0.83/0.98  gc_basic_clause_elim:                   0
% 0.83/0.98  forced_gc_time:                         0
% 0.83/0.98  parsing_time:                           0.007
% 0.83/0.98  unif_index_cands_time:                  0.
% 0.83/0.98  unif_index_add_time:                    0.
% 0.83/0.98  orderings_time:                         0.
% 0.83/0.98  out_proof_time:                         0.011
% 0.83/0.98  total_time:                             0.068
% 0.83/0.98  num_of_symbols:                         46
% 0.83/0.98  num_of_terms:                           947
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing
% 0.83/0.98  
% 0.83/0.98  num_of_splits:                          0
% 0.83/0.98  num_of_split_atoms:                     0
% 0.83/0.98  num_of_reused_defs:                     0
% 0.83/0.98  num_eq_ax_congr_red:                    0
% 0.83/0.98  num_of_sem_filtered_clauses:            0
% 0.83/0.98  num_of_subtypes:                        4
% 0.83/0.98  monotx_restored_types:                  0
% 0.83/0.98  sat_num_of_epr_types:                   0
% 0.83/0.98  sat_num_of_non_cyclic_types:            0
% 0.83/0.98  sat_guarded_non_collapsed_types:        0
% 0.83/0.98  num_pure_diseq_elim:                    0
% 0.83/0.98  simp_replaced_by:                       0
% 0.83/0.98  res_preprocessed:                       30
% 0.83/0.98  prep_upred:                             0
% 0.83/0.98  prep_unflattend:                        0
% 0.83/0.98  smt_new_axioms:                         0
% 0.83/0.98  pred_elim_cands:                        5
% 0.83/0.98  pred_elim:                              2
% 0.83/0.98  pred_elim_cl:                           2
% 0.83/0.98  pred_elim_cycles:                       8
% 0.83/0.98  merged_defs:                            0
% 0.83/0.98  merged_defs_ncl:                        0
% 0.83/0.98  bin_hyper_res:                          0
% 0.83/0.98  prep_cycles:                            2
% 0.83/0.98  pred_elim_time:                         0.017
% 0.83/0.98  splitting_time:                         0.
% 0.83/0.98  sem_filter_time:                        0.
% 0.83/0.98  monotx_time:                            0.
% 0.83/0.98  subtype_inf_time:                       0.
% 0.83/0.98  
% 0.83/0.98  ------ Problem properties
% 0.83/0.98  
% 0.83/0.98  clauses:                                14
% 0.83/0.98  conjectures:                            5
% 0.83/0.98  epr:                                    5
% 0.83/0.98  horn:                                   9
% 0.83/0.98  ground:                                 5
% 0.83/0.98  unary:                                  1
% 0.83/0.98  binary:                                 5
% 0.83/0.98  lits:                                   39
% 0.83/0.98  lits_eq:                                0
% 0.83/0.98  fd_pure:                                0
% 0.83/0.98  fd_pseudo:                              0
% 0.83/0.98  fd_cond:                                0
% 0.83/0.98  fd_pseudo_cond:                         0
% 0.83/0.98  ac_symbols:                             0
% 0.83/0.98  
% 0.83/0.98  ------ Propositional Solver
% 0.83/0.98  
% 0.83/0.98  prop_solver_calls:                      15
% 0.83/0.98  prop_fast_solver_calls:                 520
% 0.83/0.98  smt_solver_calls:                       0
% 0.83/0.98  smt_fast_solver_calls:                  0
% 0.83/0.98  prop_num_of_clauses:                    330
% 0.83/0.98  prop_preprocess_simplified:             1386
% 0.83/0.98  prop_fo_subsumed:                       37
% 0.83/0.98  prop_solver_time:                       0.
% 0.83/0.98  smt_solver_time:                        0.
% 0.83/0.98  smt_fast_solver_time:                   0.
% 0.83/0.98  prop_fast_solver_time:                  0.
% 0.83/0.98  prop_unsat_core_time:                   0.
% 0.83/0.98  
% 0.83/0.98  ------ QBF
% 0.83/0.98  
% 0.83/0.98  qbf_q_res:                              0
% 0.83/0.98  qbf_num_tautologies:                    0
% 0.83/0.98  qbf_prep_cycles:                        0
% 0.83/0.98  
% 0.83/0.98  ------ BMC1
% 0.83/0.98  
% 0.83/0.98  bmc1_current_bound:                     -1
% 0.83/0.98  bmc1_last_solved_bound:                 -1
% 0.83/0.98  bmc1_unsat_core_size:                   -1
% 0.83/0.98  bmc1_unsat_core_parents_size:           -1
% 0.83/0.98  bmc1_merge_next_fun:                    0
% 0.83/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.83/0.98  
% 0.83/0.98  ------ Instantiation
% 0.83/0.98  
% 0.83/0.98  inst_num_of_clauses:                    39
% 0.83/0.98  inst_num_in_passive:                    5
% 0.83/0.98  inst_num_in_active:                     31
% 0.83/0.98  inst_num_in_unprocessed:                2
% 0.83/0.98  inst_num_of_loops:                      53
% 0.83/0.98  inst_num_of_learning_restarts:          0
% 0.83/0.98  inst_num_moves_active_passive:          18
% 0.83/0.98  inst_lit_activity:                      0
% 0.83/0.98  inst_lit_activity_moves:                0
% 0.83/0.98  inst_num_tautologies:                   0
% 0.83/0.98  inst_num_prop_implied:                  0
% 0.83/0.98  inst_num_existing_simplified:           0
% 0.83/0.98  inst_num_eq_res_simplified:             0
% 0.83/0.98  inst_num_child_elim:                    0
% 0.83/0.98  inst_num_of_dismatching_blockings:      8
% 0.83/0.98  inst_num_of_non_proper_insts:           18
% 0.83/0.98  inst_num_of_duplicates:                 0
% 0.83/0.98  inst_inst_num_from_inst_to_res:         0
% 0.83/0.98  inst_dismatching_checking_time:         0.
% 0.83/0.98  
% 0.83/0.98  ------ Resolution
% 0.83/0.98  
% 0.83/0.98  res_num_of_clauses:                     0
% 0.83/0.98  res_num_in_passive:                     0
% 0.83/0.98  res_num_in_active:                      0
% 0.83/0.98  res_num_of_loops:                       32
% 0.83/0.98  res_forward_subset_subsumed:            0
% 0.83/0.98  res_backward_subset_subsumed:           0
% 0.83/0.98  res_forward_subsumed:                   0
% 0.83/0.98  res_backward_subsumed:                  0
% 0.83/0.98  res_forward_subsumption_resolution:     3
% 0.83/0.98  res_backward_subsumption_resolution:    0
% 0.83/0.98  res_clause_to_clause_subsumption:       23
% 0.83/0.98  res_orphan_elimination:                 0
% 0.83/0.98  res_tautology_del:                      0
% 0.83/0.98  res_num_eq_res_simplified:              0
% 0.83/0.98  res_num_sel_changes:                    0
% 0.83/0.98  res_moves_from_active_to_pass:          0
% 0.83/0.98  
% 0.83/0.98  ------ Superposition
% 0.83/0.98  
% 0.83/0.98  sup_time_total:                         0.
% 0.83/0.98  sup_time_generating:                    0.
% 0.83/0.98  sup_time_sim_full:                      0.
% 0.83/0.98  sup_time_sim_immed:                     0.
% 0.83/0.98  
% 0.83/0.98  sup_num_of_clauses:                     0
% 0.83/0.98  sup_num_in_active:                      0
% 0.83/0.98  sup_num_in_passive:                     0
% 0.83/0.98  sup_num_of_loops:                       0
% 0.83/0.98  sup_fw_superposition:                   0
% 0.83/0.98  sup_bw_superposition:                   0
% 0.83/0.98  sup_immediate_simplified:               0
% 0.83/0.98  sup_given_eliminated:                   0
% 0.83/0.98  comparisons_done:                       0
% 0.83/0.98  comparisons_avoided:                    0
% 0.83/0.98  
% 0.83/0.98  ------ Simplifications
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  sim_fw_subset_subsumed:                 0
% 0.83/0.98  sim_bw_subset_subsumed:                 0
% 0.83/0.98  sim_fw_subsumed:                        0
% 0.83/0.98  sim_bw_subsumed:                        0
% 0.83/0.98  sim_fw_subsumption_res:                 0
% 0.83/0.98  sim_bw_subsumption_res:                 0
% 0.83/0.98  sim_tautology_del:                      0
% 0.83/0.98  sim_eq_tautology_del:                   0
% 0.83/0.98  sim_eq_res_simp:                        0
% 0.83/0.98  sim_fw_demodulated:                     0
% 0.83/0.98  sim_bw_demodulated:                     0
% 0.83/0.98  sim_light_normalised:                   0
% 0.83/0.98  sim_joinable_taut:                      0
% 0.83/0.98  sim_joinable_simp:                      0
% 0.83/0.98  sim_ac_normalised:                      0
% 0.83/0.98  sim_smt_subsumption:                    0
% 0.83/0.98  
%------------------------------------------------------------------------------

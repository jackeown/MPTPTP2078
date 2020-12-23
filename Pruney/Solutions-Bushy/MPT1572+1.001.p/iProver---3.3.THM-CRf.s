%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1572+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:55 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 797 expanded)
%              Number of clauses        :  127 ( 217 expanded)
%              Number of leaves         :    9 ( 212 expanded)
%              Depth                    :   15
%              Number of atoms          :  780 (5949 expanded)
%              Number of equality atoms :  152 ( 152 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
        & r1_yellow_0(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | sP0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f14])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | sP0(X0,X1) )
     => ( ( ~ r2_yellow_0(X0,sK4)
          & r2_yellow_0(X0,k3_xboole_0(sK4,u1_struct_0(X0))) )
        | ( ~ r2_yellow_0(X0,k3_xboole_0(sK4,u1_struct_0(X0)))
          & r2_yellow_0(X0,sK4) )
        | ( ~ r1_yellow_0(X0,sK4)
          & r1_yellow_0(X0,k3_xboole_0(sK4,u1_struct_0(X0))) )
        | sP0(X0,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,X1)
              & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              & r2_yellow_0(X0,X1) )
            | ( ~ r1_yellow_0(X0,X1)
              & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            | sP0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK3,X1)
            & r2_yellow_0(sK3,k3_xboole_0(X1,u1_struct_0(sK3))) )
          | ( ~ r2_yellow_0(sK3,k3_xboole_0(X1,u1_struct_0(sK3)))
            & r2_yellow_0(sK3,X1) )
          | ( ~ r1_yellow_0(sK3,X1)
            & r1_yellow_0(sK3,k3_xboole_0(X1,u1_struct_0(sK3))) )
          | sP0(sK3,X1) )
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ( ~ r2_yellow_0(sK3,sK4)
        & r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) )
      | ( ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
        & r2_yellow_0(sK3,sK4) )
      | ( ~ r1_yellow_0(sK3,sK4)
        & r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) )
      | sP0(sK3,sK4) )
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f26,f25])).

fof(f41,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK1(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK1(X0,X1,X2))
          | r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK1(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK1(X0,X1,X2))
              | r2_lattice3(X0,X1,sK1(X0,X1,X2)) )
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
        & r1_yellow_0(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,
    ( ~ r2_yellow_0(sK3,sK4)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r1_yellow_0(sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r2_yellow_0(sK3,sK4)
    | ~ r1_yellow_0(sK3,sK4)
    | sP0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,
    ( ~ r2_yellow_0(sK3,sK4)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | sP0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r2_yellow_0(sK3,sK4)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | sP0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_316,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ r1_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_21])).

cnf(c_321,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_903,plain,
    ( ~ r1_lattice3(sK3,X0_43,X0_44)
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_1108,plain,
    ( ~ r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | ~ m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_1114,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) != iProver_top
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) = iProver_top
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1116,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_336,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | r1_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_21])).

cnf(c_341,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_902,plain,
    ( r1_lattice3(sK3,X0_43,X0_44)
    | ~ r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_341])).

cnf(c_1109,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | ~ r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | ~ m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_1110,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) = iProver_top
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) != iProver_top
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_1112,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1088,plain,
    ( ~ r1_lattice3(sK3,X0_43,sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ m1_subset_1(sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_1094,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_1096,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_1089,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ m1_subset_1(sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_1090,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r1_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_1092,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_372,plain,
    ( r1_lattice3(sK3,X0,sK2(sK3,X1,X0))
    | r1_lattice3(sK3,X1,sK2(sK3,X1,X0))
    | ~ r2_yellow_0(sK3,X1)
    | r2_yellow_0(sK3,X0)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

cnf(c_374,plain,
    ( r2_yellow_0(sK3,X0)
    | ~ r2_yellow_0(sK3,X1)
    | r1_lattice3(sK3,X1,sK2(sK3,X1,X0))
    | r1_lattice3(sK3,X0,sK2(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_21])).

cnf(c_375,plain,
    ( r1_lattice3(sK3,X0,sK2(sK3,X1,X0))
    | r1_lattice3(sK3,X1,sK2(sK3,X1,X0))
    | ~ r2_yellow_0(sK3,X1)
    | r2_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_900,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X1_43,X0_43))
    | r1_lattice3(sK3,X1_43,sK2(sK3,X1_43,X0_43))
    | ~ r2_yellow_0(sK3,X1_43)
    | r2_yellow_0(sK3,X0_43) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_1081,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK3,X0_43)
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1082,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r2_yellow_0(sK3,X0_43) != iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_1084,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r2_yellow_0(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_3,plain,
    ( ~ r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_391,plain,
    ( ~ r1_lattice3(sK3,X0,sK2(sK3,X1,X0))
    | ~ r1_lattice3(sK3,X1,sK2(sK3,X1,X0))
    | ~ r2_yellow_0(sK3,X1)
    | r2_yellow_0(sK3,X0)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_20])).

cnf(c_393,plain,
    ( r2_yellow_0(sK3,X0)
    | ~ r2_yellow_0(sK3,X1)
    | ~ r1_lattice3(sK3,X1,sK2(sK3,X1,X0))
    | ~ r1_lattice3(sK3,X0,sK2(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_21])).

cnf(c_394,plain,
    ( ~ r1_lattice3(sK3,X0,sK2(sK3,X1,X0))
    | ~ r1_lattice3(sK3,X1,sK2(sK3,X1,X0))
    | ~ r2_yellow_0(sK3,X1)
    | r2_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_899,plain,
    ( ~ r1_lattice3(sK3,X0_43,sK2(sK3,X1_43,X0_43))
    | ~ r1_lattice3(sK3,X1_43,sK2(sK3,X1_43,X0_43))
    | ~ r2_yellow_0(sK3,X1_43)
    | r2_yellow_0(sK3,X0_43) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_1076,plain,
    ( ~ r1_lattice3(sK3,X0_43,sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK3,X0_43)
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_1077,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r2_yellow_0(sK3,X0_43) != iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_1079,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r2_yellow_0(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_5,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r2_yellow_0(X0,X2)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_356,plain,
    ( ~ r2_yellow_0(sK3,X0)
    | r2_yellow_0(sK3,X1)
    | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_20])).

cnf(c_358,plain,
    ( m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3))
    | r2_yellow_0(sK3,X1)
    | ~ r2_yellow_0(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_21])).

cnf(c_359,plain,
    ( ~ r2_yellow_0(sK3,X0)
    | r2_yellow_0(sK3,X1)
    | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_901,plain,
    ( ~ r2_yellow_0(sK3,X0_43)
    | r2_yellow_0(sK3,X1_43)
    | m1_subset_1(sK2(sK3,X0_43,X1_43),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_1069,plain,
    ( ~ r2_yellow_0(sK3,X0_43)
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_1070,plain,
    ( r2_yellow_0(sK3,X0_43) != iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK2(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_1072,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r2_yellow_0(sK3,sK4) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_1056,plain,
    ( r2_yellow_0(sK3,X0_43)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_1057,plain,
    ( r2_yellow_0(sK3,X0_43) = iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_1059,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r2_yellow_0(sK3,sK4) = iProver_top
    | m1_subset_1(sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1046,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | r2_yellow_0(sK3,X0_43)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1052,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) = iProver_top
    | r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) = iProver_top
    | r2_yellow_0(sK3,X0_43) = iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_1054,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r2_yellow_0(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1047,plain,
    ( ~ r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | ~ r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | r2_yellow_0(sK3,X0_43)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_1048,plain,
    ( r1_lattice3(sK3,X0_43,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) != iProver_top
    | r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) != iProver_top
    | r2_yellow_0(sK3,X0_43) = iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_1050,plain,
    ( r1_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | r1_lattice3(sK3,sK4,sK2(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r2_yellow_0(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_276,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_9,c_20])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ r2_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_21])).

cnf(c_281,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_905,plain,
    ( ~ r2_lattice3(sK3,X0_43,X0_44)
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_1026,plain,
    ( ~ r2_lattice3(sK3,X0_43,sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ m1_subset_1(sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1042,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_1044,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_296,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_8,c_20])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | r2_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_21])).

cnf(c_301,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k3_xboole_0(X0,u1_struct_0(sK3)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_904,plain,
    ( r2_lattice3(sK3,X0_43,X0_44)
    | ~ r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_1027,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ m1_subset_1(sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_1038,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(sK3,X1_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_1040,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1,plain,
    ( r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_lattice3(X0,X2,sK1(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_426,plain,
    ( r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | r2_lattice3(sK3,X1,sK1(sK3,X1,X0))
    | ~ r1_yellow_0(sK3,X1)
    | r1_yellow_0(sK3,X0)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_1,c_20])).

cnf(c_428,plain,
    ( r1_yellow_0(sK3,X0)
    | ~ r1_yellow_0(sK3,X1)
    | r2_lattice3(sK3,X1,sK1(sK3,X1,X0))
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_21])).

cnf(c_429,plain,
    ( r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | r2_lattice3(sK3,X1,sK1(sK3,X1,X0))
    | ~ r1_yellow_0(sK3,X1)
    | r1_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_428])).

cnf(c_897,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X1_43,X0_43))
    | r2_lattice3(sK3,X1_43,sK1(sK3,X1_43,X0_43))
    | ~ r1_yellow_0(sK3,X1_43)
    | r1_yellow_0(sK3,X0_43) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_1021,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r1_yellow_0(sK3,X0_43)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_1022,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r1_yellow_0(sK3,X0_43) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_1024,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r1_yellow_0(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_0,plain,
    ( ~ r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK1(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_445,plain,
    ( ~ r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X1,sK1(sK3,X1,X0))
    | ~ r1_yellow_0(sK3,X1)
    | r1_yellow_0(sK3,X0)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_20])).

cnf(c_447,plain,
    ( r1_yellow_0(sK3,X0)
    | ~ r1_yellow_0(sK3,X1)
    | ~ r2_lattice3(sK3,X1,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,sK1(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_21])).

cnf(c_448,plain,
    ( ~ r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X1,sK1(sK3,X1,X0))
    | ~ r1_yellow_0(sK3,X1)
    | r1_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_896,plain,
    ( ~ r2_lattice3(sK3,X0_43,sK1(sK3,X1_43,X0_43))
    | ~ r2_lattice3(sK3,X1_43,sK1(sK3,X1_43,X0_43))
    | ~ r1_yellow_0(sK3,X1_43)
    | r1_yellow_0(sK3,X0_43) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_1016,plain,
    ( ~ r2_lattice3(sK3,X0_43,sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))))
    | ~ r1_yellow_0(sK3,X0_43)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_1017,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r1_yellow_0(sK3,X0_43) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_1019,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3)))) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r1_yellow_0(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_2,plain,
    ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_410,plain,
    ( m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,X0)
    | r1_yellow_0(sK3,X1)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_412,plain,
    ( r1_yellow_0(sK3,X1)
    | ~ r1_yellow_0(sK3,X0)
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_21])).

cnf(c_413,plain,
    ( m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,X0)
    | r1_yellow_0(sK3,X1) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_898,plain,
    ( m1_subset_1(sK1(sK3,X0_43,X1_43),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,X0_43)
    | r1_yellow_0(sK3,X1_43) ),
    inference(subtyping,[status(esa)],[c_413])).

cnf(c_1010,plain,
    ( m1_subset_1(sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,X0_43)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1011,plain,
    ( m1_subset_1(sK1(sK3,X0_43,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,X0_43) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_1013,plain,
    ( m1_subset_1(sK1(sK3,sK4,k3_xboole_0(sK4,u1_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r1_yellow_0(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_989,plain,
    ( ~ r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | ~ m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1005,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) != iProver_top
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) = iProver_top
    | m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_1007,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_990,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | ~ r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43))
    | ~ m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_1001,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) = iProver_top
    | r2_lattice3(sK3,k3_xboole_0(X0_43,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43)) != iProver_top
    | m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X1_43),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_1003,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_984,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | r1_yellow_0(sK3,X0_43)
    | ~ r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_985,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) = iProver_top
    | r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) = iProver_top
    | r1_yellow_0(sK3,X0_43) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_987,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r1_yellow_0(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_979,plain,
    ( ~ r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | ~ r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43))
    | r1_yellow_0(sK3,X0_43)
    | ~ r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_980,plain,
    ( r2_lattice3(sK3,X0_43,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) != iProver_top
    | r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43)) != iProver_top
    | r1_yellow_0(sK3,X0_43) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_982,plain,
    ( r2_lattice3(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | r2_lattice3(sK3,sK4,sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4)) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r1_yellow_0(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_974,plain,
    ( m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43),u1_struct_0(sK3))
    | r1_yellow_0(sK3,X0_43)
    | ~ r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_975,plain,
    ( m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),X0_43),u1_struct_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,X0_43) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_977,plain,
    ( m1_subset_1(sK1(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)),sK4),u1_struct_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r1_yellow_0(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1)
    | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,negated_conjecture,
    ( sP0(sK3,sK4)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r2_yellow_0(sK3,sK4)
    | ~ r1_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_241,plain,
    ( ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r2_yellow_0(sK3,sK4)
    | ~ r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r1_yellow_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_242,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r2_yellow_0(sK3,sK4) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r1_yellow_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_18,negated_conjecture,
    ( sP0(sK3,sK4)
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r2_yellow_0(sK3,sK4)
    | ~ r1_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_225,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r2_yellow_0(sK3,sK4)
    | ~ r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r1_yellow_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_10,c_18])).

cnf(c_226,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r2_yellow_0(sK3,sK4) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r1_yellow_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1)
    | r1_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( sP0(sK3,sK4)
    | ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r2_yellow_0(sK3,sK4)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_208,plain,
    ( ~ r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | ~ r2_yellow_0(sK3,sK4)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r1_yellow_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_209,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) != iProver_top
    | r2_yellow_0(sK3,sK4) != iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r1_yellow_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_19,negated_conjecture,
    ( sP0(sK3,sK4)
    | r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r2_yellow_0(sK3,sK4)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_192,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r2_yellow_0(sK3,sK4)
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3)))
    | r1_yellow_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_11,c_19])).

cnf(c_193,plain,
    ( r2_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r2_yellow_0(sK3,sK4) = iProver_top
    | r1_yellow_0(sK3,k3_xboole_0(sK4,u1_struct_0(sK3))) = iProver_top
    | r1_yellow_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1116,c_1112,c_1096,c_1092,c_1084,c_1079,c_1072,c_1059,c_1054,c_1050,c_1044,c_1040,c_1024,c_1019,c_1013,c_1007,c_1003,c_987,c_982,c_977,c_242,c_226,c_209,c_193])).


%------------------------------------------------------------------------------

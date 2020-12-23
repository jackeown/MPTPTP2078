%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2012+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:01 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 114 expanded)
%              Number of clauses        :   36 (  45 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 319 expanded)
%              Number of equality atoms :   89 ( 143 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v6_waybel_0(X1,X0) )
         => ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | u1_orders_2(X1) != k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | u1_orders_2(X1) != k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( u1_orders_2(k3_waybel_9(X0)) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(X1)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f31,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_11,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_246,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_406,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_4,plain,
    ( ~ v6_waybel_0(k3_waybel_9(X0),X0)
    | ~ l1_waybel_0(k3_waybel_9(X0),X0)
    | ~ l1_orders_2(X0)
    | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( v6_waybel_0(k3_waybel_9(X0),X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( l1_waybel_0(k3_waybel_9(X0),X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_78,plain,
    ( ~ l1_orders_2(X0)
    | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7,c_6])).

cnf(c_244,plain,
    ( ~ l1_orders_2(X0_41)
    | k3_relset_1(u1_struct_0(X0_41),u1_struct_0(X0_41),u1_orders_2(X0_41)) = u1_orders_2(k3_waybel_9(X0_41)) ),
    inference(subtyping,[status(esa)],[c_78])).

cnf(c_408,plain,
    ( k3_relset_1(u1_struct_0(X0_41),u1_struct_0(X0_41),u1_orders_2(X0_41)) = u1_orders_2(k3_waybel_9(X0_41))
    | l1_orders_2(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_1025,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = u1_orders_2(k3_waybel_9(sK0)) ),
    inference(superposition,[status(thm)],[c_406,c_408])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_249,plain,
    ( ~ l1_orders_2(X0_41)
    | g1_orders_2(u1_struct_0(X0_41),k3_relset_1(u1_struct_0(X0_41),u1_struct_0(X0_41),u1_orders_2(X0_41))) = k7_lattice3(X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_404,plain,
    ( g1_orders_2(u1_struct_0(X0_41),k3_relset_1(u1_struct_0(X0_41),u1_struct_0(X0_41),u1_orders_2(X0_41))) = k7_lattice3(X0_41)
    | l1_orders_2(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_628,plain,
    ( g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) = k7_lattice3(sK0) ),
    inference(superposition,[status(thm)],[c_406,c_404])).

cnf(c_1111,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) = k7_lattice3(sK0) ),
    inference(demodulation,[status(thm)],[c_1025,c_628])).

cnf(c_255,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_652,plain,
    ( g1_orders_2(u1_struct_0(X0_41),u1_orders_2(k3_waybel_9(sK0))) != X1_41
    | g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != X1_41
    | g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = g1_orders_2(u1_struct_0(X0_41),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_803,plain,
    ( g1_orders_2(u1_struct_0(X0_41),u1_orders_2(k3_waybel_9(sK0))) != k7_lattice3(sK0)
    | g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = g1_orders_2(u1_struct_0(X0_41),u1_orders_2(k3_waybel_9(sK0)))
    | g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != k7_lattice3(sK0) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_805,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0)))
    | g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != k7_lattice3(sK0)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) != k7_lattice3(sK0) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_5,plain,
    ( ~ v6_waybel_0(k3_waybel_9(X0),X0)
    | ~ l1_waybel_0(k3_waybel_9(X0),X0)
    | ~ l1_orders_2(X0)
    | u1_struct_0(k3_waybel_9(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_71,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(k3_waybel_9(X0)) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_7,c_6])).

cnf(c_245,plain,
    ( ~ l1_orders_2(X0_41)
    | u1_struct_0(k3_waybel_9(X0_41)) = u1_struct_0(X0_41) ),
    inference(subtyping,[status(esa)],[c_71])).

cnf(c_407,plain,
    ( u1_struct_0(k3_waybel_9(X0_41)) = u1_struct_0(X0_41)
    | l1_orders_2(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_465,plain,
    ( u1_struct_0(k3_waybel_9(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_406,c_407])).

cnf(c_10,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_247,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_509,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(demodulation,[status(thm)],[c_465,c_247])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | v1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_160,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | k7_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_161,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(k7_lattice3(X0))
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_165,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_161,c_8])).

cnf(c_242,plain,
    ( ~ l1_orders_2(X0_41)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0_41)),u1_orders_2(k7_lattice3(X0_41))) = k7_lattice3(X0_41) ),
    inference(subtyping,[status(esa)],[c_165])).

cnf(c_295,plain,
    ( ~ l1_orders_2(sK0)
    | g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) = k7_lattice3(sK0) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1111,c_805,c_509,c_295,c_11])).


%------------------------------------------------------------------------------

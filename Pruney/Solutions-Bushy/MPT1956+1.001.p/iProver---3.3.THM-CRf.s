%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1956+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:55 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 411 expanded)
%              Number of clauses        :   34 (  72 expanded)
%              Number of leaves         :    9 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  304 (2767 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
          | ~ r3_orders_2(X0,k1_yellow_0(X0,sK1),k1_yellow_0(X0,sK2)) )
        & r1_tarski(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
            | ~ r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
      | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25])).

fof(f41,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_7,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
    | ~ r1_tarski(X2,X1)
    | ~ r2_yellow_0(X0,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_214,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
    | ~ r2_yellow_0(X0,sK1)
    | ~ r2_yellow_0(X0,sK2)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_10,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_297,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ r2_yellow_0(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_214,c_10])).

cnf(c_4,plain,
    ( r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_179,plain,
    ( r2_yellow_0(sK0,X0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_4,c_11])).

cnf(c_13,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,negated_conjecture,
    ( v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_44,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_183,plain,
    ( r2_yellow_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_179,c_13,c_12,c_10,c_44])).

cnf(c_305,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_297,c_183,c_183])).

cnf(c_8,negated_conjecture,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_328,plain,
    ( ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_305,c_8])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_153,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_155,plain,
    ( ~ v2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_153,c_12,c_10,c_44])).

cnf(c_264,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | r3_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[status(thm)],[c_2,c_155])).

cnf(c_14,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_268,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | r3_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_14,c_10])).

cnf(c_336,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_328,c_268])).

cnf(c_6,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_tarski(X1,X2)
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_197,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,sK1),k1_yellow_0(X0,sK2))
    | ~ r1_yellow_0(X0,sK1)
    | ~ r1_yellow_0(X0,sK2)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_6,c_9])).

cnf(c_308,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_197,c_10])).

cnf(c_5,plain,
    ( r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_165,plain,
    ( r1_yellow_0(sK0,X0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_5,c_11])).

cnf(c_169,plain,
    ( r1_yellow_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165,c_13,c_12,c_10,c_44])).

cnf(c_316,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_308,c_169,c_169])).

cnf(c_338,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_316])).

cnf(c_1,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_319,plain,
    ( m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_346,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_338,c_319,c_319])).


%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1506+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:44 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 153 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :    8 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 ( 897 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
          & r3_lattice3(X0,X1,X2) )
     => ( ~ r3_lattices(X0,X1,k16_lattice3(X0,sK3))
        & r3_lattice3(X0,X1,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,sK2,k16_lattice3(X0,X2))
            & r3_lattice3(X0,sK2,X2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
                & r3_lattice3(X0,X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK1,X1,k16_lattice3(sK1,X2))
              & r3_lattice3(sK1,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v4_lattice3(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
    & r3_lattice3(sK1,sK2,sK3)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v4_lattice3(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f20,f19,f18])).

fof(f35,plain,(
    ~ r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK0(X0,X1,X2),X2)
        & sK0(X0,X1,X2) = X0
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK0(X0,X1,X2),X2)
            & sK0(X0,X1,X2) = X0
            & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f34,plain,(
    r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,negated_conjecture,
    ( ~ r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,X2)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | k15_lattice3(X1,X2) != k16_lattice3(sK1,sK3)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_218,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,X0)
    | ~ v10_lattices(sK1)
    | ~ v4_lattice3(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | k15_lattice3(sK1,X0) != k16_lattice3(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_222,plain,
    ( ~ r2_hidden(sK2,X0)
    | k15_lattice3(sK1,X0) != k16_lattice3(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_13,c_12,c_11,c_10,c_9])).

cnf(c_517,plain,
    ( ~ r2_hidden(sK2,X0_45)
    | k15_lattice3(sK1,X0_45) != k16_lattice3(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_724,plain,
    ( ~ r2_hidden(sK2,a_2_1_lattice3(sK1,sK3))
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_0,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_296,plain,
    ( v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_297,plain,
    ( v2_struct_0(sK1)
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0)) = k16_lattice3(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_301,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,X0)) = k16_lattice3(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_13])).

cnf(c_516,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_45)) = k16_lattice3(sK1,X0_45) ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_538,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) = k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,negated_conjecture,
    ( r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK3 != X2
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_179,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,a_2_1_lattice3(sK1,sK3))
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_724,c_538,c_179,c_9,c_10,c_13])).


%------------------------------------------------------------------------------

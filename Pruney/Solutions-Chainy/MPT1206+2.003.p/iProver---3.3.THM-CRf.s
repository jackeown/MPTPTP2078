%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:17 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 206 expanded)
%              Number of clauses        :   36 (  51 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (1011 expanded)
%              Number of equality atoms :   82 ( 193 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),X1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v13_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v13_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f30,f29])).

fof(f42,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f43,plain,(
    v13_lattices(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_370,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_611,plain,
    ( k2_lattices(sK1,k5_lattices(sK1),sK2) != X0_42
    | k5_lattices(sK1) != X0_42
    | k5_lattices(sK1) = k2_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_665,plain,
    ( k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1)
    | k5_lattices(sK1) = k2_lattices(sK1,k5_lattices(sK1),sK2)
    | k5_lattices(sK1) != k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_369,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_660,plain,
    ( k5_lattices(sK1) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v6_lattices(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_151,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v6_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_152,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | v6_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_43,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | v6_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_154,plain,
    ( v6_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_152,c_14,c_13,c_11,c_43])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_154])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | k4_lattices(sK1,X1,X0) = k2_lattices(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_7,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_24,plain,
    ( l1_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k4_lattices(sK1,X1,X0) = k2_lattices(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_174,c_14,c_11,c_24])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | k4_lattices(sK1,X1_42,X0_42) = k2_lattices(sK1,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_178])).

cnf(c_581,plain,
    ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k4_lattices(sK1,k5_lattices(sK1),sK2) = k2_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_566,plain,
    ( k4_lattices(sK1,k5_lattices(sK1),sK2) != X0_42
    | k5_lattices(sK1) != X0_42
    | k5_lattices(sK1) = k4_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_580,plain,
    ( k4_lattices(sK1,k5_lattices(sK1),sK2) != k2_lattices(sK1,k5_lattices(sK1),sK2)
    | k5_lattices(sK1) = k4_lattices(sK1,k5_lattices(sK1),sK2)
    | k5_lattices(sK1) != k2_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,negated_conjecture,
    ( v13_lattices(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_6,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_27,plain,
    ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_14,c_11,c_24,c_27])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),X0_42) = k5_lattices(sK1) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),sK2) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_9,negated_conjecture,
    ( k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_367,negated_conjecture,
    ( k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_665,c_660,c_581,c_580,c_384,c_367,c_27,c_24,c_10,c_11,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n018.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 18:54:42 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 0.81/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.81/0.96  
% 0.81/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.81/0.96  
% 0.81/0.96  ------  iProver source info
% 0.81/0.96  
% 0.81/0.96  git: date: 2020-06-30 10:37:57 +0100
% 0.81/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.81/0.96  git: non_committed_changes: false
% 0.81/0.96  git: last_make_outside_of_git: false
% 0.81/0.96  
% 0.81/0.96  ------ 
% 0.81/0.96  
% 0.81/0.96  ------ Input Options
% 0.81/0.96  
% 0.81/0.96  --out_options                           all
% 0.81/0.96  --tptp_safe_out                         true
% 0.81/0.96  --problem_path                          ""
% 0.81/0.96  --include_path                          ""
% 0.81/0.96  --clausifier                            res/vclausify_rel
% 0.81/0.96  --clausifier_options                    --mode clausify
% 0.81/0.96  --stdin                                 false
% 0.81/0.96  --stats_out                             all
% 0.81/0.96  
% 0.81/0.96  ------ General Options
% 0.81/0.96  
% 0.81/0.96  --fof                                   false
% 0.81/0.96  --time_out_real                         305.
% 0.81/0.96  --time_out_virtual                      -1.
% 0.81/0.96  --symbol_type_check                     false
% 0.81/0.96  --clausify_out                          false
% 0.81/0.96  --sig_cnt_out                           false
% 0.81/0.96  --trig_cnt_out                          false
% 0.81/0.96  --trig_cnt_out_tolerance                1.
% 0.81/0.96  --trig_cnt_out_sk_spl                   false
% 0.81/0.96  --abstr_cl_out                          false
% 0.81/0.96  
% 0.81/0.96  ------ Global Options
% 0.81/0.96  
% 0.81/0.96  --schedule                              default
% 0.81/0.96  --add_important_lit                     false
% 0.81/0.96  --prop_solver_per_cl                    1000
% 0.81/0.96  --min_unsat_core                        false
% 0.81/0.96  --soft_assumptions                      false
% 0.81/0.96  --soft_lemma_size                       3
% 0.81/0.96  --prop_impl_unit_size                   0
% 0.81/0.96  --prop_impl_unit                        []
% 0.81/0.96  --share_sel_clauses                     true
% 0.81/0.96  --reset_solvers                         false
% 0.81/0.96  --bc_imp_inh                            [conj_cone]
% 0.81/0.96  --conj_cone_tolerance                   3.
% 0.81/0.96  --extra_neg_conj                        none
% 0.81/0.96  --large_theory_mode                     true
% 0.81/0.96  --prolific_symb_bound                   200
% 0.81/0.96  --lt_threshold                          2000
% 0.81/0.96  --clause_weak_htbl                      true
% 0.81/0.96  --gc_record_bc_elim                     false
% 0.81/0.96  
% 0.81/0.96  ------ Preprocessing Options
% 0.81/0.96  
% 0.81/0.96  --preprocessing_flag                    true
% 0.81/0.96  --time_out_prep_mult                    0.1
% 0.81/0.96  --splitting_mode                        input
% 0.81/0.96  --splitting_grd                         true
% 0.81/0.96  --splitting_cvd                         false
% 0.81/0.96  --splitting_cvd_svl                     false
% 0.81/0.96  --splitting_nvd                         32
% 0.81/0.96  --sub_typing                            true
% 0.81/0.96  --prep_gs_sim                           true
% 0.81/0.96  --prep_unflatten                        true
% 0.81/0.96  --prep_res_sim                          true
% 0.81/0.96  --prep_upred                            true
% 0.81/0.96  --prep_sem_filter                       exhaustive
% 0.81/0.96  --prep_sem_filter_out                   false
% 0.81/0.96  --pred_elim                             true
% 0.81/0.96  --res_sim_input                         true
% 0.81/0.96  --eq_ax_congr_red                       true
% 0.81/0.96  --pure_diseq_elim                       true
% 0.81/0.96  --brand_transform                       false
% 0.81/0.96  --non_eq_to_eq                          false
% 0.81/0.96  --prep_def_merge                        true
% 0.81/0.96  --prep_def_merge_prop_impl              false
% 0.81/0.96  --prep_def_merge_mbd                    true
% 0.81/0.96  --prep_def_merge_tr_red                 false
% 0.81/0.96  --prep_def_merge_tr_cl                  false
% 0.81/0.96  --smt_preprocessing                     true
% 0.81/0.96  --smt_ac_axioms                         fast
% 0.81/0.96  --preprocessed_out                      false
% 0.81/0.96  --preprocessed_stats                    false
% 0.81/0.96  
% 0.81/0.96  ------ Abstraction refinement Options
% 0.81/0.96  
% 0.81/0.96  --abstr_ref                             []
% 0.81/0.96  --abstr_ref_prep                        false
% 0.81/0.96  --abstr_ref_until_sat                   false
% 0.81/0.96  --abstr_ref_sig_restrict                funpre
% 0.81/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/0.96  --abstr_ref_under                       []
% 0.81/0.96  
% 0.81/0.96  ------ SAT Options
% 0.81/0.96  
% 0.81/0.96  --sat_mode                              false
% 0.81/0.96  --sat_fm_restart_options                ""
% 0.81/0.96  --sat_gr_def                            false
% 0.81/0.96  --sat_epr_types                         true
% 0.81/0.96  --sat_non_cyclic_types                  false
% 0.81/0.96  --sat_finite_models                     false
% 0.81/0.96  --sat_fm_lemmas                         false
% 0.81/0.96  --sat_fm_prep                           false
% 0.81/0.96  --sat_fm_uc_incr                        true
% 0.81/0.96  --sat_out_model                         small
% 0.81/0.96  --sat_out_clauses                       false
% 0.81/0.96  
% 0.81/0.96  ------ QBF Options
% 0.81/0.96  
% 0.81/0.96  --qbf_mode                              false
% 0.81/0.96  --qbf_elim_univ                         false
% 0.81/0.96  --qbf_dom_inst                          none
% 0.81/0.96  --qbf_dom_pre_inst                      false
% 0.81/0.96  --qbf_sk_in                             false
% 0.81/0.96  --qbf_pred_elim                         true
% 0.81/0.96  --qbf_split                             512
% 0.81/0.96  
% 0.81/0.96  ------ BMC1 Options
% 0.81/0.96  
% 0.81/0.96  --bmc1_incremental                      false
% 0.81/0.96  --bmc1_axioms                           reachable_all
% 0.81/0.96  --bmc1_min_bound                        0
% 0.81/0.96  --bmc1_max_bound                        -1
% 0.81/0.96  --bmc1_max_bound_default                -1
% 0.81/0.96  --bmc1_symbol_reachability              true
% 0.81/0.96  --bmc1_property_lemmas                  false
% 0.81/0.96  --bmc1_k_induction                      false
% 0.81/0.96  --bmc1_non_equiv_states                 false
% 0.81/0.96  --bmc1_deadlock                         false
% 0.81/0.96  --bmc1_ucm                              false
% 0.81/0.96  --bmc1_add_unsat_core                   none
% 0.81/0.96  --bmc1_unsat_core_children              false
% 0.81/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/0.96  --bmc1_out_stat                         full
% 0.81/0.96  --bmc1_ground_init                      false
% 0.81/0.96  --bmc1_pre_inst_next_state              false
% 0.81/0.96  --bmc1_pre_inst_state                   false
% 0.81/0.96  --bmc1_pre_inst_reach_state             false
% 0.81/0.96  --bmc1_out_unsat_core                   false
% 0.81/0.96  --bmc1_aig_witness_out                  false
% 0.81/0.96  --bmc1_verbose                          false
% 0.81/0.96  --bmc1_dump_clauses_tptp                false
% 0.81/0.96  --bmc1_dump_unsat_core_tptp             false
% 0.81/0.96  --bmc1_dump_file                        -
% 0.81/0.96  --bmc1_ucm_expand_uc_limit              128
% 0.81/0.96  --bmc1_ucm_n_expand_iterations          6
% 0.81/0.96  --bmc1_ucm_extend_mode                  1
% 0.81/0.96  --bmc1_ucm_init_mode                    2
% 0.81/0.96  --bmc1_ucm_cone_mode                    none
% 0.81/0.96  --bmc1_ucm_reduced_relation_type        0
% 0.81/0.96  --bmc1_ucm_relax_model                  4
% 0.81/0.96  --bmc1_ucm_full_tr_after_sat            true
% 0.81/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/0.96  --bmc1_ucm_layered_model                none
% 0.81/0.96  --bmc1_ucm_max_lemma_size               10
% 0.81/0.96  
% 0.81/0.96  ------ AIG Options
% 0.81/0.96  
% 0.81/0.96  --aig_mode                              false
% 0.81/0.96  
% 0.81/0.96  ------ Instantiation Options
% 0.81/0.96  
% 0.81/0.96  --instantiation_flag                    true
% 0.81/0.96  --inst_sos_flag                         false
% 0.81/0.96  --inst_sos_phase                        true
% 0.81/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/0.96  --inst_lit_sel_side                     num_symb
% 0.81/0.96  --inst_solver_per_active                1400
% 0.81/0.96  --inst_solver_calls_frac                1.
% 0.81/0.96  --inst_passive_queue_type               priority_queues
% 0.81/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/0.96  --inst_passive_queues_freq              [25;2]
% 0.81/0.96  --inst_dismatching                      true
% 0.81/0.96  --inst_eager_unprocessed_to_passive     true
% 0.81/0.96  --inst_prop_sim_given                   true
% 0.81/0.96  --inst_prop_sim_new                     false
% 0.81/0.96  --inst_subs_new                         false
% 0.81/0.96  --inst_eq_res_simp                      false
% 0.81/0.96  --inst_subs_given                       false
% 0.81/0.96  --inst_orphan_elimination               true
% 0.81/0.96  --inst_learning_loop_flag               true
% 0.81/0.96  --inst_learning_start                   3000
% 0.81/0.96  --inst_learning_factor                  2
% 0.81/0.96  --inst_start_prop_sim_after_learn       3
% 0.81/0.96  --inst_sel_renew                        solver
% 0.81/0.96  --inst_lit_activity_flag                true
% 0.81/0.96  --inst_restr_to_given                   false
% 0.81/0.96  --inst_activity_threshold               500
% 0.81/0.96  --inst_out_proof                        true
% 0.81/0.96  
% 0.81/0.96  ------ Resolution Options
% 0.81/0.96  
% 0.81/0.96  --resolution_flag                       true
% 0.81/0.96  --res_lit_sel                           adaptive
% 0.81/0.96  --res_lit_sel_side                      none
% 0.81/0.96  --res_ordering                          kbo
% 0.81/0.96  --res_to_prop_solver                    active
% 0.81/0.96  --res_prop_simpl_new                    false
% 0.81/0.96  --res_prop_simpl_given                  true
% 0.81/0.96  --res_passive_queue_type                priority_queues
% 0.81/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/0.96  --res_passive_queues_freq               [15;5]
% 0.81/0.96  --res_forward_subs                      full
% 0.81/0.96  --res_backward_subs                     full
% 0.81/0.96  --res_forward_subs_resolution           true
% 0.81/0.96  --res_backward_subs_resolution          true
% 0.81/0.96  --res_orphan_elimination                true
% 0.81/0.96  --res_time_limit                        2.
% 0.81/0.96  --res_out_proof                         true
% 0.81/0.96  
% 0.81/0.96  ------ Superposition Options
% 0.81/0.96  
% 0.81/0.96  --superposition_flag                    true
% 0.81/0.96  --sup_passive_queue_type                priority_queues
% 0.81/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/0.96  --sup_passive_queues_freq               [8;1;4]
% 0.81/0.96  --demod_completeness_check              fast
% 0.81/0.96  --demod_use_ground                      true
% 0.81/0.96  --sup_to_prop_solver                    passive
% 0.81/0.96  --sup_prop_simpl_new                    true
% 0.81/0.96  --sup_prop_simpl_given                  true
% 0.81/0.96  --sup_fun_splitting                     false
% 0.81/0.96  --sup_smt_interval                      50000
% 0.81/0.96  
% 0.81/0.96  ------ Superposition Simplification Setup
% 0.81/0.96  
% 0.81/0.96  --sup_indices_passive                   []
% 0.81/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.96  --sup_full_bw                           [BwDemod]
% 0.81/0.96  --sup_immed_triv                        [TrivRules]
% 0.81/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.96  --sup_immed_bw_main                     []
% 0.81/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.96  
% 0.81/0.96  ------ Combination Options
% 0.81/0.96  
% 0.81/0.96  --comb_res_mult                         3
% 0.81/0.96  --comb_sup_mult                         2
% 0.81/0.96  --comb_inst_mult                        10
% 0.81/0.96  
% 0.81/0.96  ------ Debug Options
% 0.81/0.96  
% 0.81/0.96  --dbg_backtrace                         false
% 0.81/0.96  --dbg_dump_prop_clauses                 false
% 0.81/0.96  --dbg_dump_prop_clauses_file            -
% 0.81/0.96  --dbg_out_stat                          false
% 0.81/0.96  ------ Parsing...
% 0.81/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.81/0.96  
% 0.81/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.81/0.96  
% 0.81/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.81/0.96  
% 0.81/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.81/0.96  ------ Proving...
% 0.81/0.96  ------ Problem Properties 
% 0.81/0.96  
% 0.81/0.96  
% 0.81/0.96  clauses                                 8
% 0.81/0.96  conjectures                             2
% 0.81/0.96  EPR                                     0
% 0.81/0.96  Horn                                    7
% 0.81/0.96  unary                                   3
% 0.81/0.96  binary                                  2
% 0.81/0.96  lits                                    17
% 0.81/0.96  lits eq                                 8
% 0.81/0.96  fd_pure                                 0
% 0.81/0.96  fd_pseudo                               0
% 0.81/0.96  fd_cond                                 2
% 0.81/0.96  fd_pseudo_cond                          0
% 0.81/0.96  AC symbols                              0
% 0.81/0.96  
% 0.81/0.96  ------ Schedule dynamic 5 is on 
% 0.81/0.96  
% 0.81/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.81/0.96  
% 0.81/0.96  
% 0.81/0.96  ------ 
% 0.81/0.96  Current options:
% 0.81/0.96  ------ 
% 0.81/0.96  
% 0.81/0.96  ------ Input Options
% 0.81/0.96  
% 0.81/0.96  --out_options                           all
% 0.81/0.96  --tptp_safe_out                         true
% 0.81/0.96  --problem_path                          ""
% 0.81/0.96  --include_path                          ""
% 0.81/0.96  --clausifier                            res/vclausify_rel
% 0.81/0.96  --clausifier_options                    --mode clausify
% 0.81/0.96  --stdin                                 false
% 0.81/0.96  --stats_out                             all
% 0.81/0.96  
% 0.81/0.96  ------ General Options
% 0.81/0.96  
% 0.81/0.96  --fof                                   false
% 0.81/0.96  --time_out_real                         305.
% 0.81/0.96  --time_out_virtual                      -1.
% 0.81/0.96  --symbol_type_check                     false
% 0.81/0.96  --clausify_out                          false
% 0.81/0.96  --sig_cnt_out                           false
% 0.81/0.96  --trig_cnt_out                          false
% 0.81/0.96  --trig_cnt_out_tolerance                1.
% 0.81/0.96  --trig_cnt_out_sk_spl                   false
% 0.81/0.96  --abstr_cl_out                          false
% 0.81/0.96  
% 0.81/0.96  ------ Global Options
% 0.81/0.96  
% 0.81/0.96  --schedule                              default
% 0.81/0.96  --add_important_lit                     false
% 0.81/0.96  --prop_solver_per_cl                    1000
% 0.81/0.96  --min_unsat_core                        false
% 0.81/0.96  --soft_assumptions                      false
% 0.81/0.96  --soft_lemma_size                       3
% 0.81/0.96  --prop_impl_unit_size                   0
% 0.81/0.96  --prop_impl_unit                        []
% 0.81/0.96  --share_sel_clauses                     true
% 0.81/0.96  --reset_solvers                         false
% 0.81/0.96  --bc_imp_inh                            [conj_cone]
% 0.81/0.96  --conj_cone_tolerance                   3.
% 0.81/0.96  --extra_neg_conj                        none
% 0.81/0.96  --large_theory_mode                     true
% 0.81/0.96  --prolific_symb_bound                   200
% 0.81/0.96  --lt_threshold                          2000
% 0.81/0.96  --clause_weak_htbl                      true
% 0.81/0.96  --gc_record_bc_elim                     false
% 0.81/0.96  
% 0.81/0.96  ------ Preprocessing Options
% 0.81/0.96  
% 0.81/0.96  --preprocessing_flag                    true
% 0.81/0.96  --time_out_prep_mult                    0.1
% 0.81/0.96  --splitting_mode                        input
% 0.81/0.96  --splitting_grd                         true
% 0.81/0.96  --splitting_cvd                         false
% 0.81/0.96  --splitting_cvd_svl                     false
% 0.81/0.96  --splitting_nvd                         32
% 0.81/0.96  --sub_typing                            true
% 0.81/0.96  --prep_gs_sim                           true
% 0.81/0.96  --prep_unflatten                        true
% 0.81/0.96  --prep_res_sim                          true
% 0.81/0.96  --prep_upred                            true
% 0.81/0.96  --prep_sem_filter                       exhaustive
% 0.81/0.96  --prep_sem_filter_out                   false
% 0.81/0.96  --pred_elim                             true
% 0.81/0.96  --res_sim_input                         true
% 0.81/0.96  --eq_ax_congr_red                       true
% 0.81/0.96  --pure_diseq_elim                       true
% 0.81/0.96  --brand_transform                       false
% 0.81/0.96  --non_eq_to_eq                          false
% 0.81/0.96  --prep_def_merge                        true
% 0.81/0.96  --prep_def_merge_prop_impl              false
% 0.81/0.96  --prep_def_merge_mbd                    true
% 0.81/0.96  --prep_def_merge_tr_red                 false
% 0.81/0.96  --prep_def_merge_tr_cl                  false
% 0.81/0.96  --smt_preprocessing                     true
% 0.81/0.96  --smt_ac_axioms                         fast
% 0.81/0.96  --preprocessed_out                      false
% 0.81/0.96  --preprocessed_stats                    false
% 0.81/0.96  
% 0.81/0.96  ------ Abstraction refinement Options
% 0.81/0.96  
% 0.81/0.96  --abstr_ref                             []
% 0.81/0.96  --abstr_ref_prep                        false
% 0.81/0.96  --abstr_ref_until_sat                   false
% 0.81/0.96  --abstr_ref_sig_restrict                funpre
% 0.81/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/0.96  --abstr_ref_under                       []
% 0.81/0.96  
% 0.81/0.96  ------ SAT Options
% 0.81/0.96  
% 0.81/0.96  --sat_mode                              false
% 0.81/0.96  --sat_fm_restart_options                ""
% 0.81/0.96  --sat_gr_def                            false
% 0.81/0.96  --sat_epr_types                         true
% 0.81/0.96  --sat_non_cyclic_types                  false
% 0.81/0.96  --sat_finite_models                     false
% 0.81/0.96  --sat_fm_lemmas                         false
% 0.81/0.96  --sat_fm_prep                           false
% 0.81/0.96  --sat_fm_uc_incr                        true
% 0.81/0.96  --sat_out_model                         small
% 0.81/0.96  --sat_out_clauses                       false
% 0.81/0.96  
% 0.81/0.96  ------ QBF Options
% 0.81/0.96  
% 0.81/0.96  --qbf_mode                              false
% 0.81/0.96  --qbf_elim_univ                         false
% 0.81/0.96  --qbf_dom_inst                          none
% 0.81/0.96  --qbf_dom_pre_inst                      false
% 0.81/0.96  --qbf_sk_in                             false
% 0.81/0.96  --qbf_pred_elim                         true
% 0.81/0.96  --qbf_split                             512
% 0.81/0.96  
% 0.81/0.96  ------ BMC1 Options
% 0.81/0.96  
% 0.81/0.96  --bmc1_incremental                      false
% 0.81/0.96  --bmc1_axioms                           reachable_all
% 0.81/0.96  --bmc1_min_bound                        0
% 0.81/0.96  --bmc1_max_bound                        -1
% 0.81/0.96  --bmc1_max_bound_default                -1
% 0.81/0.96  --bmc1_symbol_reachability              true
% 0.81/0.96  --bmc1_property_lemmas                  false
% 0.81/0.96  --bmc1_k_induction                      false
% 0.81/0.96  --bmc1_non_equiv_states                 false
% 0.81/0.96  --bmc1_deadlock                         false
% 0.81/0.96  --bmc1_ucm                              false
% 0.81/0.96  --bmc1_add_unsat_core                   none
% 0.81/0.96  --bmc1_unsat_core_children              false
% 0.81/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/0.96  --bmc1_out_stat                         full
% 0.81/0.96  --bmc1_ground_init                      false
% 0.81/0.96  --bmc1_pre_inst_next_state              false
% 0.81/0.96  --bmc1_pre_inst_state                   false
% 0.81/0.96  --bmc1_pre_inst_reach_state             false
% 0.81/0.96  --bmc1_out_unsat_core                   false
% 0.81/0.96  --bmc1_aig_witness_out                  false
% 0.81/0.96  --bmc1_verbose                          false
% 0.81/0.96  --bmc1_dump_clauses_tptp                false
% 0.81/0.96  --bmc1_dump_unsat_core_tptp             false
% 0.81/0.96  --bmc1_dump_file                        -
% 0.81/0.96  --bmc1_ucm_expand_uc_limit              128
% 0.81/0.96  --bmc1_ucm_n_expand_iterations          6
% 0.81/0.96  --bmc1_ucm_extend_mode                  1
% 0.81/0.96  --bmc1_ucm_init_mode                    2
% 0.81/0.96  --bmc1_ucm_cone_mode                    none
% 0.81/0.96  --bmc1_ucm_reduced_relation_type        0
% 0.81/0.96  --bmc1_ucm_relax_model                  4
% 0.81/0.96  --bmc1_ucm_full_tr_after_sat            true
% 0.81/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/0.96  --bmc1_ucm_layered_model                none
% 0.81/0.96  --bmc1_ucm_max_lemma_size               10
% 0.81/0.96  
% 0.81/0.96  ------ AIG Options
% 0.81/0.96  
% 0.81/0.96  --aig_mode                              false
% 0.81/0.96  
% 0.81/0.96  ------ Instantiation Options
% 0.81/0.96  
% 0.81/0.96  --instantiation_flag                    true
% 0.81/0.96  --inst_sos_flag                         false
% 0.81/0.96  --inst_sos_phase                        true
% 0.81/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/0.96  --inst_lit_sel_side                     none
% 0.81/0.96  --inst_solver_per_active                1400
% 0.81/0.96  --inst_solver_calls_frac                1.
% 0.81/0.96  --inst_passive_queue_type               priority_queues
% 0.81/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/0.96  --inst_passive_queues_freq              [25;2]
% 0.81/0.96  --inst_dismatching                      true
% 0.81/0.96  --inst_eager_unprocessed_to_passive     true
% 0.81/0.96  --inst_prop_sim_given                   true
% 0.81/0.96  --inst_prop_sim_new                     false
% 0.81/0.96  --inst_subs_new                         false
% 0.81/0.96  --inst_eq_res_simp                      false
% 0.81/0.96  --inst_subs_given                       false
% 0.81/0.96  --inst_orphan_elimination               true
% 0.81/0.96  --inst_learning_loop_flag               true
% 0.81/0.96  --inst_learning_start                   3000
% 0.81/0.96  --inst_learning_factor                  2
% 0.81/0.96  --inst_start_prop_sim_after_learn       3
% 0.81/0.96  --inst_sel_renew                        solver
% 0.81/0.96  --inst_lit_activity_flag                true
% 0.81/0.96  --inst_restr_to_given                   false
% 0.81/0.96  --inst_activity_threshold               500
% 0.81/0.96  --inst_out_proof                        true
% 0.81/0.96  
% 0.81/0.96  ------ Resolution Options
% 0.81/0.96  
% 0.81/0.96  --resolution_flag                       false
% 0.81/0.96  --res_lit_sel                           adaptive
% 0.81/0.96  --res_lit_sel_side                      none
% 0.81/0.96  --res_ordering                          kbo
% 0.81/0.96  --res_to_prop_solver                    active
% 0.81/0.96  --res_prop_simpl_new                    false
% 0.81/0.96  --res_prop_simpl_given                  true
% 0.81/0.96  --res_passive_queue_type                priority_queues
% 0.81/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/0.96  --res_passive_queues_freq               [15;5]
% 0.81/0.96  --res_forward_subs                      full
% 0.81/0.96  --res_backward_subs                     full
% 0.81/0.96  --res_forward_subs_resolution           true
% 0.81/0.96  --res_backward_subs_resolution          true
% 0.81/0.96  --res_orphan_elimination                true
% 0.81/0.96  --res_time_limit                        2.
% 0.81/0.96  --res_out_proof                         true
% 0.81/0.96  
% 0.81/0.96  ------ Superposition Options
% 0.81/0.96  
% 0.81/0.96  --superposition_flag                    true
% 0.81/0.96  --sup_passive_queue_type                priority_queues
% 0.81/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/0.96  --sup_passive_queues_freq               [8;1;4]
% 0.81/0.96  --demod_completeness_check              fast
% 0.81/0.96  --demod_use_ground                      true
% 0.81/0.96  --sup_to_prop_solver                    passive
% 0.81/0.96  --sup_prop_simpl_new                    true
% 0.81/0.96  --sup_prop_simpl_given                  true
% 0.81/0.96  --sup_fun_splitting                     false
% 0.81/0.96  --sup_smt_interval                      50000
% 0.81/0.96  
% 0.81/0.96  ------ Superposition Simplification Setup
% 0.81/0.96  
% 0.81/0.96  --sup_indices_passive                   []
% 0.81/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.96  --sup_full_bw                           [BwDemod]
% 0.81/0.96  --sup_immed_triv                        [TrivRules]
% 0.81/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.96  --sup_immed_bw_main                     []
% 0.81/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.96  
% 0.81/0.96  ------ Combination Options
% 0.81/0.96  
% 0.81/0.96  --comb_res_mult                         3
% 0.81/0.96  --comb_sup_mult                         2
% 0.81/0.96  --comb_inst_mult                        10
% 0.81/0.96  
% 0.81/0.96  ------ Debug Options
% 0.81/0.96  
% 0.81/0.96  --dbg_backtrace                         false
% 0.81/0.96  --dbg_dump_prop_clauses                 false
% 0.81/0.96  --dbg_dump_prop_clauses_file            -
% 0.81/0.96  --dbg_out_stat                          false
% 0.81/0.96  
% 0.81/0.96  
% 0.81/0.96  
% 0.81/0.96  
% 0.81/0.96  ------ Proving...
% 0.81/0.96  
% 0.81/0.96  
% 0.81/0.96  % SZS status Theorem for theBenchmark.p
% 0.81/0.96  
% 0.81/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 0.81/0.96  
% 0.81/0.96  fof(f5,axiom,(
% 0.81/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 0.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.96  
% 0.81/0.96  fof(f21,plain,(
% 0.81/0.96    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.81/0.96    inference(ennf_transformation,[],[f5])).
% 0.81/0.96  
% 0.81/0.96  fof(f22,plain,(
% 0.81/0.96    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.81/0.96    inference(flattening,[],[f21])).
% 0.81/0.96  
% 0.81/0.96  fof(f40,plain,(
% 0.81/0.96    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.81/0.96    inference(cnf_transformation,[],[f22])).
% 0.81/0.96  
% 0.81/0.96  fof(f1,axiom,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.96  
% 0.81/0.96  fof(f9,plain,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.81/0.96    inference(pure_predicate_removal,[],[f1])).
% 0.81/0.96  
% 0.81/0.96  fof(f10,plain,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.81/0.96    inference(pure_predicate_removal,[],[f9])).
% 0.81/0.96  
% 0.81/0.96  fof(f11,plain,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.81/0.96    inference(pure_predicate_removal,[],[f10])).
% 0.81/0.96  
% 0.81/0.96  fof(f12,plain,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.81/0.96    inference(pure_predicate_removal,[],[f11])).
% 0.81/0.96  
% 0.81/0.96  fof(f13,plain,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.81/0.96    inference(pure_predicate_removal,[],[f12])).
% 0.81/0.96  
% 0.81/0.96  fof(f14,plain,(
% 0.81/0.96    ! [X0] : (((v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.81/0.96    inference(ennf_transformation,[],[f13])).
% 0.81/0.96  
% 0.81/0.96  fof(f15,plain,(
% 0.81/0.96    ! [X0] : ((v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.81/0.96    inference(flattening,[],[f14])).
% 0.81/0.96  
% 0.81/0.96  fof(f33,plain,(
% 0.81/0.96    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.81/0.96    inference(cnf_transformation,[],[f15])).
% 0.81/0.96  
% 0.81/0.96  fof(f6,conjecture,(
% 0.81/0.96    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.96  
% 0.81/0.96  fof(f7,negated_conjecture,(
% 0.81/0.96    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.81/0.96    inference(negated_conjecture,[],[f6])).
% 0.81/0.96  
% 0.81/0.96  fof(f23,plain,(
% 0.81/0.96    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.81/0.96    inference(ennf_transformation,[],[f7])).
% 0.81/0.96  
% 0.81/0.96  fof(f24,plain,(
% 0.81/0.96    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.81/0.96    inference(flattening,[],[f23])).
% 0.81/0.96  
% 0.81/0.96  fof(f30,plain,(
% 0.81/0.96    ( ! [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 0.81/0.96    introduced(choice_axiom,[])).
% 0.81/0.96  
% 0.81/0.96  fof(f29,plain,(
% 0.81/0.96    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),X1) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v13_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.81/0.96    introduced(choice_axiom,[])).
% 0.81/0.96  
% 0.81/0.96  fof(f31,plain,(
% 0.81/0.96    (k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v13_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 0.81/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f30,f29])).
% 0.81/0.96  
% 0.81/0.96  fof(f42,plain,(
% 0.81/0.96    v10_lattices(sK1)),
% 0.81/0.96    inference(cnf_transformation,[],[f31])).
% 0.81/0.96  
% 0.81/0.96  fof(f41,plain,(
% 0.81/0.96    ~v2_struct_0(sK1)),
% 0.81/0.96    inference(cnf_transformation,[],[f31])).
% 0.81/0.96  
% 0.81/0.96  fof(f44,plain,(
% 0.81/0.96    l3_lattices(sK1)),
% 0.81/0.96    inference(cnf_transformation,[],[f31])).
% 0.81/0.96  
% 0.81/0.96  fof(f4,axiom,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.96  
% 0.81/0.96  fof(f8,plain,(
% 0.81/0.96    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.81/0.96    inference(pure_predicate_removal,[],[f4])).
% 0.81/0.96  
% 0.81/0.96  fof(f20,plain,(
% 0.81/0.96    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.81/0.96    inference(ennf_transformation,[],[f8])).
% 0.81/0.96  
% 0.81/0.96  fof(f39,plain,(
% 0.81/0.96    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.81/0.96    inference(cnf_transformation,[],[f20])).
% 0.81/0.96  
% 0.81/0.96  fof(f2,axiom,(
% 0.81/0.96    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.96  
% 0.81/0.96  fof(f16,plain,(
% 0.81/0.96    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.81/0.96    inference(ennf_transformation,[],[f2])).
% 0.81/0.96  
% 0.81/0.96  fof(f17,plain,(
% 0.81/0.96    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.81/0.96    inference(flattening,[],[f16])).
% 0.81/0.96  
% 0.81/0.96  fof(f25,plain,(
% 0.81/0.96    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.81/0.96    inference(nnf_transformation,[],[f17])).
% 0.81/0.96  
% 0.81/0.96  fof(f26,plain,(
% 0.81/0.96    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.81/0.96    inference(rectify,[],[f25])).
% 0.81/0.96  
% 0.81/0.96  fof(f27,plain,(
% 0.81/0.96    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 0.81/0.96    introduced(choice_axiom,[])).
% 0.81/0.96  
% 0.81/0.96  fof(f28,plain,(
% 0.81/0.96    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.81/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 0.81/0.96  
% 0.81/0.96  fof(f34,plain,(
% 0.81/0.96    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.81/0.96    inference(cnf_transformation,[],[f28])).
% 0.81/0.96  
% 0.81/0.96  fof(f48,plain,(
% 0.81/0.96    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.81/0.96    inference(equality_resolution,[],[f34])).
% 0.81/0.96  
% 0.81/0.96  fof(f43,plain,(
% 0.81/0.96    v13_lattices(sK1)),
% 0.81/0.96    inference(cnf_transformation,[],[f31])).
% 0.81/0.96  
% 0.81/0.96  fof(f3,axiom,(
% 0.81/0.96    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.81/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.96  
% 0.81/0.96  fof(f18,plain,(
% 0.81/0.96    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.81/0.96    inference(ennf_transformation,[],[f3])).
% 0.81/0.96  
% 0.81/0.96  fof(f19,plain,(
% 0.81/0.96    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.81/0.96    inference(flattening,[],[f18])).
% 0.81/0.96  
% 0.81/0.96  fof(f38,plain,(
% 0.81/0.96    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.81/0.96    inference(cnf_transformation,[],[f19])).
% 0.81/0.96  
% 0.81/0.96  fof(f46,plain,(
% 0.81/0.96    k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2)),
% 0.81/0.96    inference(cnf_transformation,[],[f31])).
% 0.81/0.96  
% 0.81/0.96  fof(f45,plain,(
% 0.81/0.96    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.81/0.96    inference(cnf_transformation,[],[f31])).
% 0.81/0.96  
% 0.81/0.96  cnf(c_370,plain,
% 0.81/0.96      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.81/0.96      theory(equality) ).
% 0.81/0.96  
% 0.81/0.96  cnf(c_611,plain,
% 0.81/0.96      ( k2_lattices(sK1,k5_lattices(sK1),sK2) != X0_42
% 0.81/0.96      | k5_lattices(sK1) != X0_42
% 0.81/0.96      | k5_lattices(sK1) = k2_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.81/0.96      inference(instantiation,[status(thm)],[c_370]) ).
% 0.81/0.96  
% 0.81/0.96  cnf(c_665,plain,
% 0.81/0.96      ( k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1)
% 0.81/0.96      | k5_lattices(sK1) = k2_lattices(sK1,k5_lattices(sK1),sK2)
% 0.81/0.96      | k5_lattices(sK1) != k5_lattices(sK1) ),
% 0.81/0.96      inference(instantiation,[status(thm)],[c_611]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_369,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_660,plain,
% 0.81/0.97      ( k5_lattices(sK1) = k5_lattices(sK1) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_369]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_8,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.81/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.81/0.97      | ~ l1_lattices(X1)
% 0.81/0.97      | v2_struct_0(X1)
% 0.81/0.97      | ~ v6_lattices(X1)
% 0.81/0.97      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 0.81/0.97      inference(cnf_transformation,[],[f40]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_0,plain,
% 0.81/0.97      ( ~ l3_lattices(X0)
% 0.81/0.97      | v2_struct_0(X0)
% 0.81/0.97      | ~ v10_lattices(X0)
% 0.81/0.97      | v6_lattices(X0) ),
% 0.81/0.97      inference(cnf_transformation,[],[f33]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_13,negated_conjecture,
% 0.81/0.97      ( v10_lattices(sK1) ),
% 0.81/0.97      inference(cnf_transformation,[],[f42]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_151,plain,
% 0.81/0.97      ( ~ l3_lattices(X0)
% 0.81/0.97      | v2_struct_0(X0)
% 0.81/0.97      | v6_lattices(X0)
% 0.81/0.97      | sK1 != X0 ),
% 0.81/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_152,plain,
% 0.81/0.97      ( ~ l3_lattices(sK1) | v2_struct_0(sK1) | v6_lattices(sK1) ),
% 0.81/0.97      inference(unflattening,[status(thm)],[c_151]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_14,negated_conjecture,
% 0.81/0.97      ( ~ v2_struct_0(sK1) ),
% 0.81/0.97      inference(cnf_transformation,[],[f41]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_11,negated_conjecture,
% 0.81/0.97      ( l3_lattices(sK1) ),
% 0.81/0.97      inference(cnf_transformation,[],[f44]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_43,plain,
% 0.81/0.97      ( ~ l3_lattices(sK1)
% 0.81/0.97      | v2_struct_0(sK1)
% 0.81/0.97      | ~ v10_lattices(sK1)
% 0.81/0.97      | v6_lattices(sK1) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_154,plain,
% 0.81/0.97      ( v6_lattices(sK1) ),
% 0.81/0.97      inference(global_propositional_subsumption,
% 0.81/0.97                [status(thm)],
% 0.81/0.97                [c_152,c_14,c_13,c_11,c_43]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_173,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.81/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.81/0.97      | ~ l1_lattices(X1)
% 0.81/0.97      | v2_struct_0(X1)
% 0.81/0.97      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
% 0.81/0.97      | sK1 != X1 ),
% 0.81/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_154]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_174,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.81/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.81/0.97      | ~ l1_lattices(sK1)
% 0.81/0.97      | v2_struct_0(sK1)
% 0.81/0.97      | k4_lattices(sK1,X1,X0) = k2_lattices(sK1,X1,X0) ),
% 0.81/0.97      inference(unflattening,[status(thm)],[c_173]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_7,plain,
% 0.81/0.97      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 0.81/0.97      inference(cnf_transformation,[],[f39]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_24,plain,
% 0.81/0.97      ( l1_lattices(sK1) | ~ l3_lattices(sK1) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_178,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.81/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.81/0.97      | k4_lattices(sK1,X1,X0) = k2_lattices(sK1,X1,X0) ),
% 0.81/0.97      inference(global_propositional_subsumption,
% 0.81/0.97                [status(thm)],
% 0.81/0.97                [c_174,c_14,c_11,c_24]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_365,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
% 0.81/0.97      | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
% 0.81/0.97      | k4_lattices(sK1,X1_42,X0_42) = k2_lattices(sK1,X1_42,X0_42) ),
% 0.81/0.97      inference(subtyping,[status(esa)],[c_178]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_581,plain,
% 0.81/0.97      ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.81/0.97      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 0.81/0.97      | k4_lattices(sK1,k5_lattices(sK1),sK2) = k2_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_365]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_566,plain,
% 0.81/0.97      ( k4_lattices(sK1,k5_lattices(sK1),sK2) != X0_42
% 0.81/0.97      | k5_lattices(sK1) != X0_42
% 0.81/0.97      | k5_lattices(sK1) = k4_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_370]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_580,plain,
% 0.81/0.97      ( k4_lattices(sK1,k5_lattices(sK1),sK2) != k2_lattices(sK1,k5_lattices(sK1),sK2)
% 0.81/0.97      | k5_lattices(sK1) = k4_lattices(sK1,k5_lattices(sK1),sK2)
% 0.81/0.97      | k5_lattices(sK1) != k2_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_566]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_5,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.81/0.97      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 0.81/0.97      | ~ l1_lattices(X1)
% 0.81/0.97      | ~ v13_lattices(X1)
% 0.81/0.97      | v2_struct_0(X1)
% 0.81/0.97      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 0.81/0.97      inference(cnf_transformation,[],[f48]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_12,negated_conjecture,
% 0.81/0.97      ( v13_lattices(sK1) ),
% 0.81/0.97      inference(cnf_transformation,[],[f43]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_198,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.81/0.97      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 0.81/0.97      | ~ l1_lattices(X1)
% 0.81/0.97      | v2_struct_0(X1)
% 0.81/0.97      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 0.81/0.97      | sK1 != X1 ),
% 0.81/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_199,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.81/0.97      | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.81/0.97      | ~ l1_lattices(sK1)
% 0.81/0.97      | v2_struct_0(sK1)
% 0.81/0.97      | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
% 0.81/0.97      inference(unflattening,[status(thm)],[c_198]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_6,plain,
% 0.81/0.97      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 0.81/0.97      | ~ l1_lattices(X0)
% 0.81/0.97      | v2_struct_0(X0) ),
% 0.81/0.97      inference(cnf_transformation,[],[f38]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_27,plain,
% 0.81/0.97      ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.81/0.97      | ~ l1_lattices(sK1)
% 0.81/0.97      | v2_struct_0(sK1) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_203,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.81/0.97      | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
% 0.81/0.97      inference(global_propositional_subsumption,
% 0.81/0.97                [status(thm)],
% 0.81/0.97                [c_199,c_14,c_11,c_24,c_27]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_364,plain,
% 0.81/0.97      ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
% 0.81/0.97      | k2_lattices(sK1,k5_lattices(sK1),X0_42) = k5_lattices(sK1) ),
% 0.81/0.97      inference(subtyping,[status(esa)],[c_203]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_384,plain,
% 0.81/0.97      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 0.81/0.97      | k2_lattices(sK1,k5_lattices(sK1),sK2) = k5_lattices(sK1) ),
% 0.81/0.97      inference(instantiation,[status(thm)],[c_364]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_9,negated_conjecture,
% 0.81/0.97      ( k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.81/0.97      inference(cnf_transformation,[],[f46]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_367,negated_conjecture,
% 0.81/0.97      ( k5_lattices(sK1) != k4_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.81/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(c_10,negated_conjecture,
% 0.81/0.97      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.81/0.97      inference(cnf_transformation,[],[f45]) ).
% 0.81/0.97  
% 0.81/0.97  cnf(contradiction,plain,
% 0.81/0.97      ( $false ),
% 0.81/0.97      inference(minisat,
% 0.81/0.97                [status(thm)],
% 0.81/0.97                [c_665,c_660,c_581,c_580,c_384,c_367,c_27,c_24,c_10,c_11,
% 0.81/0.97                 c_14]) ).
% 0.81/0.97  
% 0.81/0.97  
% 0.81/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 0.81/0.97  
% 0.81/0.97  ------                               Statistics
% 0.81/0.97  
% 0.81/0.97  ------ General
% 0.81/0.97  
% 0.81/0.97  abstr_ref_over_cycles:                  0
% 0.81/0.97  abstr_ref_under_cycles:                 0
% 0.81/0.97  gc_basic_clause_elim:                   0
% 0.81/0.97  forced_gc_time:                         0
% 0.81/0.97  parsing_time:                           0.009
% 0.81/0.97  unif_index_cands_time:                  0.
% 0.81/0.97  unif_index_add_time:                    0.
% 0.81/0.97  orderings_time:                         0.
% 0.81/0.97  out_proof_time:                         0.008
% 0.81/0.97  total_time:                             0.055
% 0.81/0.97  num_of_symbols:                         45
% 0.81/0.97  num_of_terms:                           643
% 0.81/0.97  
% 0.81/0.97  ------ Preprocessing
% 0.81/0.97  
% 0.81/0.97  num_of_splits:                          0
% 0.81/0.97  num_of_split_atoms:                     0
% 0.81/0.97  num_of_reused_defs:                     0
% 0.81/0.97  num_eq_ax_congr_red:                    13
% 0.81/0.97  num_of_sem_filtered_clauses:            1
% 0.81/0.97  num_of_subtypes:                        3
% 0.81/0.97  monotx_restored_types:                  0
% 0.81/0.97  sat_num_of_epr_types:                   0
% 0.81/0.97  sat_num_of_non_cyclic_types:            0
% 0.81/0.97  sat_guarded_non_collapsed_types:        1
% 0.81/0.97  num_pure_diseq_elim:                    0
% 0.81/0.97  simp_replaced_by:                       0
% 0.81/0.97  res_preprocessed:                       49
% 0.81/0.97  prep_upred:                             0
% 0.81/0.97  prep_unflattend:                        8
% 0.81/0.97  smt_new_axioms:                         0
% 0.81/0.97  pred_elim_cands:                        1
% 0.81/0.97  pred_elim:                              6
% 0.81/0.97  pred_elim_cl:                           6
% 0.81/0.97  pred_elim_cycles:                       8
% 0.81/0.97  merged_defs:                            0
% 0.81/0.97  merged_defs_ncl:                        0
% 0.81/0.97  bin_hyper_res:                          0
% 0.81/0.97  prep_cycles:                            4
% 0.81/0.97  pred_elim_time:                         0.002
% 0.81/0.97  splitting_time:                         0.
% 0.81/0.97  sem_filter_time:                        0.
% 0.81/0.97  monotx_time:                            0.
% 0.81/0.97  subtype_inf_time:                       0.
% 0.81/0.97  
% 0.81/0.97  ------ Problem properties
% 0.81/0.97  
% 0.81/0.97  clauses:                                8
% 0.81/0.97  conjectures:                            2
% 0.81/0.97  epr:                                    0
% 0.81/0.97  horn:                                   7
% 0.81/0.97  ground:                                 3
% 0.81/0.97  unary:                                  3
% 0.81/0.97  binary:                                 2
% 0.81/0.97  lits:                                   17
% 0.81/0.97  lits_eq:                                8
% 0.81/0.97  fd_pure:                                0
% 0.81/0.97  fd_pseudo:                              0
% 0.81/0.97  fd_cond:                                2
% 0.81/0.97  fd_pseudo_cond:                         0
% 0.81/0.97  ac_symbols:                             0
% 0.81/0.97  
% 0.81/0.97  ------ Propositional Solver
% 0.81/0.97  
% 0.81/0.97  prop_solver_calls:                      25
% 0.81/0.97  prop_fast_solver_calls:                 304
% 0.81/0.97  smt_solver_calls:                       0
% 0.81/0.97  smt_fast_solver_calls:                  0
% 0.81/0.97  prop_num_of_clauses:                    182
% 0.81/0.97  prop_preprocess_simplified:             1223
% 0.81/0.97  prop_fo_subsumed:                       15
% 0.81/0.97  prop_solver_time:                       0.
% 0.81/0.97  smt_solver_time:                        0.
% 0.81/0.97  smt_fast_solver_time:                   0.
% 0.81/0.97  prop_fast_solver_time:                  0.
% 0.81/0.97  prop_unsat_core_time:                   0.
% 0.81/0.97  
% 0.81/0.97  ------ QBF
% 0.81/0.97  
% 0.81/0.97  qbf_q_res:                              0
% 0.81/0.97  qbf_num_tautologies:                    0
% 0.81/0.97  qbf_prep_cycles:                        0
% 0.81/0.97  
% 0.81/0.97  ------ BMC1
% 0.81/0.97  
% 0.81/0.97  bmc1_current_bound:                     -1
% 0.81/0.97  bmc1_last_solved_bound:                 -1
% 0.81/0.97  bmc1_unsat_core_size:                   -1
% 0.81/0.97  bmc1_unsat_core_parents_size:           -1
% 0.81/0.97  bmc1_merge_next_fun:                    0
% 0.81/0.97  bmc1_unsat_core_clauses_time:           0.
% 0.81/0.97  
% 0.81/0.97  ------ Instantiation
% 0.81/0.97  
% 0.81/0.97  inst_num_of_clauses:                    42
% 0.81/0.97  inst_num_in_passive:                    13
% 0.81/0.97  inst_num_in_active:                     28
% 0.81/0.97  inst_num_in_unprocessed:                0
% 0.81/0.97  inst_num_of_loops:                      34
% 0.81/0.97  inst_num_of_learning_restarts:          0
% 0.81/0.97  inst_num_moves_active_passive:          2
% 0.81/0.97  inst_lit_activity:                      0
% 0.81/0.97  inst_lit_activity_moves:                0
% 0.81/0.97  inst_num_tautologies:                   0
% 0.81/0.97  inst_num_prop_implied:                  0
% 0.81/0.97  inst_num_existing_simplified:           0
% 0.81/0.97  inst_num_eq_res_simplified:             0
% 0.81/0.97  inst_num_child_elim:                    0
% 0.81/0.97  inst_num_of_dismatching_blockings:      3
% 0.81/0.97  inst_num_of_non_proper_insts:           27
% 0.81/0.97  inst_num_of_duplicates:                 0
% 0.81/0.97  inst_inst_num_from_inst_to_res:         0
% 0.81/0.97  inst_dismatching_checking_time:         0.
% 0.81/0.97  
% 0.81/0.97  ------ Resolution
% 0.81/0.97  
% 0.81/0.97  res_num_of_clauses:                     0
% 0.81/0.97  res_num_in_passive:                     0
% 0.81/0.97  res_num_in_active:                      0
% 0.81/0.97  res_num_of_loops:                       53
% 0.81/0.97  res_forward_subset_subsumed:            1
% 0.81/0.97  res_backward_subset_subsumed:           0
% 0.81/0.97  res_forward_subsumed:                   0
% 0.81/0.97  res_backward_subsumed:                  0
% 0.81/0.97  res_forward_subsumption_resolution:     0
% 0.81/0.97  res_backward_subsumption_resolution:    0
% 0.81/0.97  res_clause_to_clause_subsumption:       23
% 0.81/0.97  res_orphan_elimination:                 0
% 0.81/0.97  res_tautology_del:                      1
% 0.81/0.97  res_num_eq_res_simplified:              0
% 0.81/0.97  res_num_sel_changes:                    0
% 0.81/0.97  res_moves_from_active_to_pass:          0
% 0.81/0.97  
% 0.81/0.97  ------ Superposition
% 0.81/0.97  
% 0.81/0.97  sup_time_total:                         0.
% 0.81/0.97  sup_time_generating:                    0.
% 0.81/0.97  sup_time_sim_full:                      0.
% 0.81/0.97  sup_time_sim_immed:                     0.
% 0.81/0.97  
% 0.81/0.97  sup_num_of_clauses:                     11
% 0.81/0.97  sup_num_in_active:                      6
% 0.81/0.97  sup_num_in_passive:                     5
% 0.81/0.97  sup_num_of_loops:                       6
% 0.81/0.97  sup_fw_superposition:                   4
% 0.81/0.97  sup_bw_superposition:                   0
% 0.81/0.97  sup_immediate_simplified:               0
% 0.81/0.97  sup_given_eliminated:                   0
% 0.81/0.97  comparisons_done:                       0
% 0.81/0.97  comparisons_avoided:                    0
% 0.81/0.97  
% 0.81/0.97  ------ Simplifications
% 0.81/0.97  
% 0.81/0.97  
% 0.81/0.97  sim_fw_subset_subsumed:                 0
% 0.81/0.97  sim_bw_subset_subsumed:                 0
% 0.81/0.97  sim_fw_subsumed:                        0
% 0.81/0.97  sim_bw_subsumed:                        0
% 0.81/0.97  sim_fw_subsumption_res:                 0
% 0.81/0.97  sim_bw_subsumption_res:                 0
% 0.81/0.97  sim_tautology_del:                      0
% 0.81/0.97  sim_eq_tautology_del:                   0
% 0.81/0.97  sim_eq_res_simp:                        0
% 0.81/0.97  sim_fw_demodulated:                     0
% 0.81/0.97  sim_bw_demodulated:                     0
% 0.81/0.97  sim_light_normalised:                   0
% 0.81/0.97  sim_joinable_taut:                      0
% 0.81/0.97  sim_joinable_simp:                      0
% 0.81/0.97  sim_ac_normalised:                      0
% 0.81/0.97  sim_smt_subsumption:                    0
% 0.81/0.97  
%------------------------------------------------------------------------------

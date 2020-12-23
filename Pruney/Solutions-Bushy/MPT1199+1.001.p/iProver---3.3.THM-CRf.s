%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1199+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:08 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 327 expanded)
%              Number of clauses        :   58 (  89 expanded)
%              Number of leaves         :    9 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  321 (2172 expanded)
%              Number of equality atoms :  110 ( 398 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_lattices(X0,X2,X1)
                    & r1_lattices(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r1_lattices(X0,X2,X1)
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2 != X1
        & r1_lattices(X0,sK2,X1)
        & r1_lattices(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK1 != X2
            & r1_lattices(X0,X2,sK1)
            & r1_lattices(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_lattices(X0,X2,X1)
                & r1_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(sK0,X2,X1)
              & r1_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l2_lattices(sK0)
      & v4_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( sK1 != sK2
    & r1_lattices(sK0,sK2,sK1)
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l2_lattices(sK0)
    & v4_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17,f16,f15])).

fof(f24,plain,(
    v4_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    r1_lattices(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_284,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_560,plain,
    ( k3_lattices(sK0,sK2,sK1) != X0_39
    | sK1 != X0_39
    | sK1 = k3_lattices(sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_561,plain,
    ( k3_lattices(sK0,sK2,sK1) != sK1
    | sK1 = k3_lattices(sK0,sK2,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( v4_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_138,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,negated_conjecture,
    ( l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_139,c_11,c_9])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0_39,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_39,u1_struct_0(sK0))
    | k3_lattices(sK0,X0_39,X1_39) = k3_lattices(sK0,X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_143])).

cnf(c_544,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_479,plain,
    ( k3_lattices(sK0,sK1,sK2) != X0_39
    | sK1 != X0_39
    | sK1 = k3_lattices(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_543,plain,
    ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,sK2,sK1)
    | sK1 != k3_lattices(sK0,sK2,sK1)
    | sK1 = k3_lattices(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_279,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_365,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_280,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_364,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_117])).

cnf(c_122,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_118,c_11,c_9])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0_39,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_39,u1_struct_0(sK0))
    | k1_lattices(sK0,X0_39,X1_39) = k3_lattices(sK0,X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_122])).

cnf(c_366,plain,
    ( k1_lattices(sK0,X0_39,X1_39) = k3_lattices(sK0,X0_39,X1_39)
    | m1_subset_1(X0_39,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_39,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_465,plain,
    ( k1_lattices(sK0,sK2,X0_39) = k3_lattices(sK0,sK2,X0_39)
    | m1_subset_1(X0_39,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_364,c_366])).

cnf(c_527,plain,
    ( k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_365,c_465])).

cnf(c_5,negated_conjecture,
    ( r1_lattices(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_167,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_168,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_168,c_11])).

cnf(c_173,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1
    | sK0 != sK0
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_173])).

cnf(c_227,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_229,plain,
    ( k1_lattices(sK0,sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_227,c_8,c_7])).

cnf(c_276,plain,
    ( k1_lattices(sK0,sK2,sK1) = sK1 ),
    inference(subtyping,[status(esa)],[c_229])).

cnf(c_529,plain,
    ( k3_lattices(sK0,sK2,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_527,c_276])).

cnf(c_450,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_435,plain,
    ( k1_lattices(sK0,sK1,sK2) != X0_39
    | sK1 != X0_39
    | sK1 = k1_lattices(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_449,plain,
    ( k1_lattices(sK0,sK1,sK2) != k3_lattices(sK0,sK1,sK2)
    | sK1 = k1_lattices(sK0,sK1,sK2)
    | sK1 != k3_lattices(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_399,plain,
    ( sK2 != X0_39
    | sK1 != X0_39
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_428,plain,
    ( sK2 != k1_lattices(sK0,sK1,sK2)
    | sK1 != k1_lattices(sK0,sK1,sK2)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_410,plain,
    ( X0_39 != X1_39
    | sK2 != X1_39
    | sK2 = X0_39 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_415,plain,
    ( X0_39 != sK2
    | sK2 = X0_39
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_424,plain,
    ( k1_lattices(sK0,sK1,sK2) != sK2
    | sK2 = k1_lattices(sK0,sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_283,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_416,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_6,negated_conjecture,
    ( r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1
    | sK0 != sK0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_173])).

cnf(c_235,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_237,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_235,c_8,c_7])).

cnf(c_275,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_4,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_281,negated_conjecture,
    ( sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_290,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_561,c_544,c_543,c_529,c_450,c_449,c_428,c_424,c_416,c_275,c_281,c_290,c_7,c_8])).


%------------------------------------------------------------------------------

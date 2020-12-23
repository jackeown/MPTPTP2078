%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:21 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 955 expanded)
%              Number of clauses        :   81 ( 225 expanded)
%              Number of leaves         :    7 ( 244 expanded)
%              Depth                    :   19
%              Number of atoms          :  612 (5215 expanded)
%              Number of equality atoms :  161 ( 932 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattices(X0,X1,X2)
              <=> ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k2_lattices(X0,X2,X1) != k5_lattices(X0)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k1_lattices(X0,X2,X1) != k6_lattices(X0)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k2_lattices(X0,X2,X1) != k5_lattices(X0)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k1_lattices(X0,X2,X1) != k6_lattices(X0)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_lattices(X0,X1,X2)
      | k2_lattices(X0,X2,X1) != k5_lattices(X0)
      | k2_lattices(X0,X1,X2) != k5_lattices(X0)
      | k1_lattices(X0,X2,X1) != k6_lattices(X0)
      | k1_lattices(X0,X1,X2) != k6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k7_lattices(X0,k7_lattices(X0,sK1)) != sK1
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k7_lattices(sK0,k7_lattices(sK0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22,f21])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ( l3_lattices(X0)
              & v16_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,X1) = X2
                <=> r2_lattices(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_lattices(X0,X1) = X2
                  | ~ r2_lattices(X0,X2,X1) )
                & ( r2_lattices(X0,X2,X1)
                  | k7_lattices(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,X1) = X2
      | ~ r2_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k6_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X2,X1) = k6_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X2,X1) != k6_lattices(X0)
    | k1_lattices(X0,X1,X2) != k6_lattices(X0)
    | k2_lattices(X0,X2,X1) != k5_lattices(X0)
    | k2_lattices(X0,X1,X2) != k5_lattices(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_335,plain,
    ( r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X2,X1) != k6_lattices(X0)
    | k1_lattices(X0,X1,X2) != k6_lattices(X0)
    | k2_lattices(X0,X2,X1) != k5_lattices(X0)
    | k2_lattices(X0,X1,X2) != k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_336,plain,
    ( r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
    | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
    | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
    | k2_lattices(sK0,X1,X0) != k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_13,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
    | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
    | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
    | k2_lattices(sK0,X1,X0) != k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_13])).

cnf(c_341,plain,
    ( r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
    | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
    | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
    | k2_lattices(sK0,X1,X0) != k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_8,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v16_lattices(X0)
    | k7_lattices(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_178,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v16_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_179,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(c_47,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | v16_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_181,plain,
    ( v16_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_179,c_16,c_14,c_13,c_47])).

cnf(c_214,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k7_lattices(X0,X2) = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_181])).

cnf(c_215,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k7_lattices(sK0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_15,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_44,plain,
    ( v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v17_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_219,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k7_lattices(sK0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_215,c_16,c_15,c_14,c_13,c_44])).

cnf(c_220,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k7_lattices(sK0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_219])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
    | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
    | k2_lattices(sK0,X1,X0) != k5_lattices(sK0)
    | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
    | k7_lattices(sK0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_341,c_220])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
    | k2_lattices(sK0,X1_44,X0_44) != k5_lattices(sK0)
    | k2_lattices(sK0,X0_44,X1_44) != k5_lattices(sK0)
    | k1_lattices(sK0,X1_44,X0_44) != k6_lattices(sK0)
    | k1_lattices(sK0,X0_44,X1_44) != k6_lattices(sK0)
    | k7_lattices(sK0,X1_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0))
    | k2_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) != k5_lattices(sK0)
    | k2_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) != k5_lattices(sK0)
    | k1_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) != k6_lattices(sK0)
    | k1_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) != k6_lattices(sK0)
    | k7_lattices(sK0,k7_lattices(sK0,X0_44)) = X0_44 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_824,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k5_lattices(sK0)
    | k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) != k5_lattices(sK0)
    | k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k6_lattices(sK0)
    | k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) != k6_lattices(sK0)
    | k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_13])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_9,plain,
    ( r2_lattices(X0,k7_lattices(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v16_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_193,plain,
    ( r2_lattices(X0,k7_lattices(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_181])).

cnf(c_194,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_198,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_194,c_16,c_15,c_14,c_13,c_44])).

cnf(c_416,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_374,c_198])).

cnf(c_7,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = k6_lattices(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_247,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X1,X2) = k6_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_248,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X0,X1) = k6_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) = k6_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_248,c_13])).

cnf(c_253,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = k6_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | X2 != X1
    | k1_lattices(sK0,X0,X2) = k6_lattices(sK0)
    | k7_lattices(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_416,c_253])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,X0),X0) = k6_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,X0),X0) = k6_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_13,c_369])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) = k6_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_646,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k6_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_6,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X2,X1) = k6_lattices(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_271,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X2,X1) = k6_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_272,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X1,X0) = k6_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X1,X0) = k6_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_13])).

cnf(c_275,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,X1,X0) = k6_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | X2 != X1
    | k1_lattices(sK0,X2,X0) = k6_lattices(sK0)
    | k7_lattices(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_416,c_275])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | k1_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_13,c_369])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | k1_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) = k6_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_492])).

cnf(c_643,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k6_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_5,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = k5_lattices(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_291,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k2_lattices(X0,X1,X2) = k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_292,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,X0,X1)
    | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_13])).

cnf(c_297,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | X2 != X1
    | k2_lattices(sK0,X0,X2) = k5_lattices(sK0)
    | k7_lattices(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_416,c_297])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_13,c_369])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_474])).

cnf(c_640,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_4,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X2,X1) = k5_lattices(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_315,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k2_lattices(X0,X2,X1) = k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_316,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k2_lattices(sK0,X1,X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,X0,X1)
    | k2_lattices(sK0,X1,X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_13])).

cnf(c_319,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,X1,X0) = k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | X2 != X1
    | k2_lattices(sK0,X2,X0) = k5_lattices(sK0)
    | k7_lattices(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_416,c_319])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | k2_lattices(sK0,X0,k7_lattices(sK0,X0)) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,k7_lattices(sK0,X0)) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_13,c_369])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | k2_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_456])).

cnf(c_637,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_631,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_11,negated_conjecture,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_609,negated_conjecture,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_824,c_646,c_643,c_640,c_637,c_631,c_609,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:56:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 0.96/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.96/0.95  
% 0.96/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.96/0.95  
% 0.96/0.95  ------  iProver source info
% 0.96/0.95  
% 0.96/0.95  git: date: 2020-06-30 10:37:57 +0100
% 0.96/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.96/0.95  git: non_committed_changes: false
% 0.96/0.95  git: last_make_outside_of_git: false
% 0.96/0.95  
% 0.96/0.95  ------ 
% 0.96/0.95  
% 0.96/0.95  ------ Input Options
% 0.96/0.95  
% 0.96/0.95  --out_options                           all
% 0.96/0.95  --tptp_safe_out                         true
% 0.96/0.95  --problem_path                          ""
% 0.96/0.95  --include_path                          ""
% 0.96/0.95  --clausifier                            res/vclausify_rel
% 0.96/0.95  --clausifier_options                    --mode clausify
% 0.96/0.95  --stdin                                 false
% 0.96/0.95  --stats_out                             all
% 0.96/0.95  
% 0.96/0.95  ------ General Options
% 0.96/0.95  
% 0.96/0.95  --fof                                   false
% 0.96/0.95  --time_out_real                         305.
% 0.96/0.95  --time_out_virtual                      -1.
% 0.96/0.95  --symbol_type_check                     false
% 0.96/0.95  --clausify_out                          false
% 0.96/0.95  --sig_cnt_out                           false
% 0.96/0.95  --trig_cnt_out                          false
% 0.96/0.95  --trig_cnt_out_tolerance                1.
% 0.96/0.95  --trig_cnt_out_sk_spl                   false
% 0.96/0.95  --abstr_cl_out                          false
% 0.96/0.95  
% 0.96/0.95  ------ Global Options
% 0.96/0.95  
% 0.96/0.95  --schedule                              default
% 0.96/0.95  --add_important_lit                     false
% 0.96/0.95  --prop_solver_per_cl                    1000
% 0.96/0.95  --min_unsat_core                        false
% 0.96/0.95  --soft_assumptions                      false
% 0.96/0.95  --soft_lemma_size                       3
% 0.96/0.95  --prop_impl_unit_size                   0
% 0.96/0.95  --prop_impl_unit                        []
% 0.96/0.95  --share_sel_clauses                     true
% 0.96/0.95  --reset_solvers                         false
% 0.96/0.95  --bc_imp_inh                            [conj_cone]
% 0.96/0.95  --conj_cone_tolerance                   3.
% 0.96/0.95  --extra_neg_conj                        none
% 0.96/0.95  --large_theory_mode                     true
% 0.96/0.95  --prolific_symb_bound                   200
% 0.96/0.95  --lt_threshold                          2000
% 0.96/0.95  --clause_weak_htbl                      true
% 0.96/0.95  --gc_record_bc_elim                     false
% 0.96/0.95  
% 0.96/0.95  ------ Preprocessing Options
% 0.96/0.95  
% 0.96/0.95  --preprocessing_flag                    true
% 0.96/0.95  --time_out_prep_mult                    0.1
% 0.96/0.95  --splitting_mode                        input
% 0.96/0.95  --splitting_grd                         true
% 0.96/0.95  --splitting_cvd                         false
% 0.96/0.95  --splitting_cvd_svl                     false
% 0.96/0.95  --splitting_nvd                         32
% 0.96/0.95  --sub_typing                            true
% 0.96/0.95  --prep_gs_sim                           true
% 0.96/0.95  --prep_unflatten                        true
% 0.96/0.95  --prep_res_sim                          true
% 0.96/0.95  --prep_upred                            true
% 0.96/0.95  --prep_sem_filter                       exhaustive
% 0.96/0.95  --prep_sem_filter_out                   false
% 0.96/0.95  --pred_elim                             true
% 0.96/0.95  --res_sim_input                         true
% 0.96/0.95  --eq_ax_congr_red                       true
% 0.96/0.95  --pure_diseq_elim                       true
% 0.96/0.95  --brand_transform                       false
% 0.96/0.95  --non_eq_to_eq                          false
% 0.96/0.95  --prep_def_merge                        true
% 0.96/0.95  --prep_def_merge_prop_impl              false
% 0.96/0.95  --prep_def_merge_mbd                    true
% 0.96/0.95  --prep_def_merge_tr_red                 false
% 0.96/0.95  --prep_def_merge_tr_cl                  false
% 0.96/0.95  --smt_preprocessing                     true
% 0.96/0.95  --smt_ac_axioms                         fast
% 0.96/0.95  --preprocessed_out                      false
% 0.96/0.95  --preprocessed_stats                    false
% 0.96/0.95  
% 0.96/0.95  ------ Abstraction refinement Options
% 0.96/0.95  
% 0.96/0.95  --abstr_ref                             []
% 0.96/0.95  --abstr_ref_prep                        false
% 0.96/0.95  --abstr_ref_until_sat                   false
% 0.96/0.95  --abstr_ref_sig_restrict                funpre
% 0.96/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.95  --abstr_ref_under                       []
% 0.96/0.95  
% 0.96/0.95  ------ SAT Options
% 0.96/0.95  
% 0.96/0.95  --sat_mode                              false
% 0.96/0.95  --sat_fm_restart_options                ""
% 0.96/0.95  --sat_gr_def                            false
% 0.96/0.95  --sat_epr_types                         true
% 0.96/0.95  --sat_non_cyclic_types                  false
% 0.96/0.95  --sat_finite_models                     false
% 0.96/0.95  --sat_fm_lemmas                         false
% 0.96/0.95  --sat_fm_prep                           false
% 0.96/0.95  --sat_fm_uc_incr                        true
% 0.96/0.95  --sat_out_model                         small
% 0.96/0.95  --sat_out_clauses                       false
% 0.96/0.95  
% 0.96/0.95  ------ QBF Options
% 0.96/0.95  
% 0.96/0.95  --qbf_mode                              false
% 0.96/0.95  --qbf_elim_univ                         false
% 0.96/0.95  --qbf_dom_inst                          none
% 0.96/0.95  --qbf_dom_pre_inst                      false
% 0.96/0.95  --qbf_sk_in                             false
% 0.96/0.95  --qbf_pred_elim                         true
% 0.96/0.95  --qbf_split                             512
% 0.96/0.95  
% 0.96/0.95  ------ BMC1 Options
% 0.96/0.95  
% 0.96/0.95  --bmc1_incremental                      false
% 0.96/0.95  --bmc1_axioms                           reachable_all
% 0.96/0.95  --bmc1_min_bound                        0
% 0.96/0.95  --bmc1_max_bound                        -1
% 0.96/0.95  --bmc1_max_bound_default                -1
% 0.96/0.95  --bmc1_symbol_reachability              true
% 0.96/0.95  --bmc1_property_lemmas                  false
% 0.96/0.95  --bmc1_k_induction                      false
% 0.96/0.95  --bmc1_non_equiv_states                 false
% 0.96/0.95  --bmc1_deadlock                         false
% 0.96/0.95  --bmc1_ucm                              false
% 0.96/0.95  --bmc1_add_unsat_core                   none
% 0.96/0.95  --bmc1_unsat_core_children              false
% 0.96/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.95  --bmc1_out_stat                         full
% 0.96/0.95  --bmc1_ground_init                      false
% 0.96/0.95  --bmc1_pre_inst_next_state              false
% 0.96/0.95  --bmc1_pre_inst_state                   false
% 0.96/0.95  --bmc1_pre_inst_reach_state             false
% 0.96/0.95  --bmc1_out_unsat_core                   false
% 0.96/0.95  --bmc1_aig_witness_out                  false
% 0.96/0.95  --bmc1_verbose                          false
% 0.96/0.95  --bmc1_dump_clauses_tptp                false
% 0.96/0.95  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.95  --bmc1_dump_file                        -
% 0.96/0.95  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.95  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.95  --bmc1_ucm_extend_mode                  1
% 0.96/0.95  --bmc1_ucm_init_mode                    2
% 0.96/0.95  --bmc1_ucm_cone_mode                    none
% 0.96/0.95  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.95  --bmc1_ucm_relax_model                  4
% 0.96/0.95  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.95  --bmc1_ucm_layered_model                none
% 0.96/0.95  --bmc1_ucm_max_lemma_size               10
% 0.96/0.95  
% 0.96/0.95  ------ AIG Options
% 0.96/0.95  
% 0.96/0.95  --aig_mode                              false
% 0.96/0.95  
% 0.96/0.95  ------ Instantiation Options
% 0.96/0.95  
% 0.96/0.95  --instantiation_flag                    true
% 0.96/0.95  --inst_sos_flag                         false
% 0.96/0.95  --inst_sos_phase                        true
% 0.96/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.95  --inst_lit_sel_side                     num_symb
% 0.96/0.95  --inst_solver_per_active                1400
% 0.96/0.95  --inst_solver_calls_frac                1.
% 0.96/0.95  --inst_passive_queue_type               priority_queues
% 0.96/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.95  --inst_passive_queues_freq              [25;2]
% 0.96/0.95  --inst_dismatching                      true
% 0.96/0.95  --inst_eager_unprocessed_to_passive     true
% 0.96/0.95  --inst_prop_sim_given                   true
% 0.96/0.95  --inst_prop_sim_new                     false
% 0.96/0.95  --inst_subs_new                         false
% 0.96/0.95  --inst_eq_res_simp                      false
% 0.96/0.95  --inst_subs_given                       false
% 0.96/0.95  --inst_orphan_elimination               true
% 0.96/0.95  --inst_learning_loop_flag               true
% 0.96/0.95  --inst_learning_start                   3000
% 0.96/0.95  --inst_learning_factor                  2
% 0.96/0.95  --inst_start_prop_sim_after_learn       3
% 0.96/0.95  --inst_sel_renew                        solver
% 0.96/0.95  --inst_lit_activity_flag                true
% 0.96/0.95  --inst_restr_to_given                   false
% 0.96/0.95  --inst_activity_threshold               500
% 0.96/0.95  --inst_out_proof                        true
% 0.96/0.95  
% 0.96/0.95  ------ Resolution Options
% 0.96/0.95  
% 0.96/0.95  --resolution_flag                       true
% 0.96/0.95  --res_lit_sel                           adaptive
% 0.96/0.95  --res_lit_sel_side                      none
% 0.96/0.95  --res_ordering                          kbo
% 0.96/0.95  --res_to_prop_solver                    active
% 0.96/0.95  --res_prop_simpl_new                    false
% 0.96/0.95  --res_prop_simpl_given                  true
% 0.96/0.95  --res_passive_queue_type                priority_queues
% 0.96/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.95  --res_passive_queues_freq               [15;5]
% 0.96/0.95  --res_forward_subs                      full
% 0.96/0.95  --res_backward_subs                     full
% 0.96/0.95  --res_forward_subs_resolution           true
% 0.96/0.95  --res_backward_subs_resolution          true
% 0.96/0.95  --res_orphan_elimination                true
% 0.96/0.95  --res_time_limit                        2.
% 0.96/0.95  --res_out_proof                         true
% 0.96/0.95  
% 0.96/0.95  ------ Superposition Options
% 0.96/0.95  
% 0.96/0.95  --superposition_flag                    true
% 0.96/0.95  --sup_passive_queue_type                priority_queues
% 0.96/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.95  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.95  --demod_completeness_check              fast
% 0.96/0.95  --demod_use_ground                      true
% 0.96/0.95  --sup_to_prop_solver                    passive
% 0.96/0.95  --sup_prop_simpl_new                    true
% 0.96/0.95  --sup_prop_simpl_given                  true
% 0.96/0.95  --sup_fun_splitting                     false
% 0.96/0.95  --sup_smt_interval                      50000
% 0.96/0.95  
% 0.96/0.95  ------ Superposition Simplification Setup
% 0.96/0.95  
% 0.96/0.95  --sup_indices_passive                   []
% 0.96/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.95  --sup_full_bw                           [BwDemod]
% 0.96/0.95  --sup_immed_triv                        [TrivRules]
% 0.96/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.95  --sup_immed_bw_main                     []
% 0.96/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.95  
% 0.96/0.95  ------ Combination Options
% 0.96/0.95  
% 0.96/0.95  --comb_res_mult                         3
% 0.96/0.95  --comb_sup_mult                         2
% 0.96/0.95  --comb_inst_mult                        10
% 0.96/0.95  
% 0.96/0.95  ------ Debug Options
% 0.96/0.95  
% 0.96/0.95  --dbg_backtrace                         false
% 0.96/0.95  --dbg_dump_prop_clauses                 false
% 0.96/0.95  --dbg_dump_prop_clauses_file            -
% 0.96/0.95  --dbg_out_stat                          false
% 0.96/0.95  ------ Parsing...
% 0.96/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.96/0.95  
% 0.96/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.96/0.95  
% 0.96/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.96/0.95  
% 0.96/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.96/0.95  ------ Proving...
% 0.96/0.95  ------ Problem Properties 
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  clauses                                 8
% 0.96/0.95  conjectures                             2
% 0.96/0.95  EPR                                     0
% 0.96/0.95  Horn                                    8
% 0.96/0.95  unary                                   2
% 0.96/0.95  binary                                  5
% 0.96/0.95  lits                                    19
% 0.96/0.95  lits eq                                 10
% 0.96/0.95  fd_pure                                 0
% 0.96/0.95  fd_pseudo                               0
% 0.96/0.95  fd_cond                                 0
% 0.96/0.95  fd_pseudo_cond                          1
% 0.96/0.95  AC symbols                              0
% 0.96/0.95  
% 0.96/0.95  ------ Schedule dynamic 5 is on 
% 0.96/0.95  
% 0.96/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  ------ 
% 0.96/0.95  Current options:
% 0.96/0.95  ------ 
% 0.96/0.95  
% 0.96/0.95  ------ Input Options
% 0.96/0.95  
% 0.96/0.95  --out_options                           all
% 0.96/0.95  --tptp_safe_out                         true
% 0.96/0.95  --problem_path                          ""
% 0.96/0.95  --include_path                          ""
% 0.96/0.95  --clausifier                            res/vclausify_rel
% 0.96/0.95  --clausifier_options                    --mode clausify
% 0.96/0.95  --stdin                                 false
% 0.96/0.95  --stats_out                             all
% 0.96/0.95  
% 0.96/0.95  ------ General Options
% 0.96/0.95  
% 0.96/0.95  --fof                                   false
% 0.96/0.95  --time_out_real                         305.
% 0.96/0.95  --time_out_virtual                      -1.
% 0.96/0.95  --symbol_type_check                     false
% 0.96/0.95  --clausify_out                          false
% 0.96/0.95  --sig_cnt_out                           false
% 0.96/0.95  --trig_cnt_out                          false
% 0.96/0.95  --trig_cnt_out_tolerance                1.
% 0.96/0.95  --trig_cnt_out_sk_spl                   false
% 0.96/0.95  --abstr_cl_out                          false
% 0.96/0.95  
% 0.96/0.95  ------ Global Options
% 0.96/0.95  
% 0.96/0.95  --schedule                              default
% 0.96/0.95  --add_important_lit                     false
% 0.96/0.95  --prop_solver_per_cl                    1000
% 0.96/0.95  --min_unsat_core                        false
% 0.96/0.95  --soft_assumptions                      false
% 0.96/0.95  --soft_lemma_size                       3
% 0.96/0.95  --prop_impl_unit_size                   0
% 0.96/0.95  --prop_impl_unit                        []
% 0.96/0.95  --share_sel_clauses                     true
% 0.96/0.95  --reset_solvers                         false
% 0.96/0.95  --bc_imp_inh                            [conj_cone]
% 0.96/0.95  --conj_cone_tolerance                   3.
% 0.96/0.95  --extra_neg_conj                        none
% 0.96/0.95  --large_theory_mode                     true
% 0.96/0.95  --prolific_symb_bound                   200
% 0.96/0.95  --lt_threshold                          2000
% 0.96/0.95  --clause_weak_htbl                      true
% 0.96/0.95  --gc_record_bc_elim                     false
% 0.96/0.95  
% 0.96/0.95  ------ Preprocessing Options
% 0.96/0.95  
% 0.96/0.95  --preprocessing_flag                    true
% 0.96/0.95  --time_out_prep_mult                    0.1
% 0.96/0.95  --splitting_mode                        input
% 0.96/0.95  --splitting_grd                         true
% 0.96/0.95  --splitting_cvd                         false
% 0.96/0.95  --splitting_cvd_svl                     false
% 0.96/0.95  --splitting_nvd                         32
% 0.96/0.95  --sub_typing                            true
% 0.96/0.95  --prep_gs_sim                           true
% 0.96/0.95  --prep_unflatten                        true
% 0.96/0.95  --prep_res_sim                          true
% 0.96/0.95  --prep_upred                            true
% 0.96/0.95  --prep_sem_filter                       exhaustive
% 0.96/0.95  --prep_sem_filter_out                   false
% 0.96/0.95  --pred_elim                             true
% 0.96/0.95  --res_sim_input                         true
% 0.96/0.95  --eq_ax_congr_red                       true
% 0.96/0.95  --pure_diseq_elim                       true
% 0.96/0.95  --brand_transform                       false
% 0.96/0.95  --non_eq_to_eq                          false
% 0.96/0.95  --prep_def_merge                        true
% 0.96/0.95  --prep_def_merge_prop_impl              false
% 0.96/0.95  --prep_def_merge_mbd                    true
% 0.96/0.95  --prep_def_merge_tr_red                 false
% 0.96/0.95  --prep_def_merge_tr_cl                  false
% 0.96/0.95  --smt_preprocessing                     true
% 0.96/0.95  --smt_ac_axioms                         fast
% 0.96/0.95  --preprocessed_out                      false
% 0.96/0.95  --preprocessed_stats                    false
% 0.96/0.95  
% 0.96/0.95  ------ Abstraction refinement Options
% 0.96/0.95  
% 0.96/0.95  --abstr_ref                             []
% 0.96/0.95  --abstr_ref_prep                        false
% 0.96/0.95  --abstr_ref_until_sat                   false
% 0.96/0.95  --abstr_ref_sig_restrict                funpre
% 0.96/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.95  --abstr_ref_under                       []
% 0.96/0.95  
% 0.96/0.95  ------ SAT Options
% 0.96/0.95  
% 0.96/0.95  --sat_mode                              false
% 0.96/0.95  --sat_fm_restart_options                ""
% 0.96/0.95  --sat_gr_def                            false
% 0.96/0.95  --sat_epr_types                         true
% 0.96/0.95  --sat_non_cyclic_types                  false
% 0.96/0.95  --sat_finite_models                     false
% 0.96/0.95  --sat_fm_lemmas                         false
% 0.96/0.95  --sat_fm_prep                           false
% 0.96/0.95  --sat_fm_uc_incr                        true
% 0.96/0.95  --sat_out_model                         small
% 0.96/0.95  --sat_out_clauses                       false
% 0.96/0.95  
% 0.96/0.95  ------ QBF Options
% 0.96/0.95  
% 0.96/0.95  --qbf_mode                              false
% 0.96/0.95  --qbf_elim_univ                         false
% 0.96/0.95  --qbf_dom_inst                          none
% 0.96/0.95  --qbf_dom_pre_inst                      false
% 0.96/0.95  --qbf_sk_in                             false
% 0.96/0.95  --qbf_pred_elim                         true
% 0.96/0.95  --qbf_split                             512
% 0.96/0.95  
% 0.96/0.95  ------ BMC1 Options
% 0.96/0.95  
% 0.96/0.95  --bmc1_incremental                      false
% 0.96/0.95  --bmc1_axioms                           reachable_all
% 0.96/0.95  --bmc1_min_bound                        0
% 0.96/0.95  --bmc1_max_bound                        -1
% 0.96/0.95  --bmc1_max_bound_default                -1
% 0.96/0.95  --bmc1_symbol_reachability              true
% 0.96/0.95  --bmc1_property_lemmas                  false
% 0.96/0.95  --bmc1_k_induction                      false
% 0.96/0.95  --bmc1_non_equiv_states                 false
% 0.96/0.95  --bmc1_deadlock                         false
% 0.96/0.95  --bmc1_ucm                              false
% 0.96/0.95  --bmc1_add_unsat_core                   none
% 0.96/0.95  --bmc1_unsat_core_children              false
% 0.96/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.95  --bmc1_out_stat                         full
% 0.96/0.95  --bmc1_ground_init                      false
% 0.96/0.95  --bmc1_pre_inst_next_state              false
% 0.96/0.95  --bmc1_pre_inst_state                   false
% 0.96/0.95  --bmc1_pre_inst_reach_state             false
% 0.96/0.95  --bmc1_out_unsat_core                   false
% 0.96/0.95  --bmc1_aig_witness_out                  false
% 0.96/0.95  --bmc1_verbose                          false
% 0.96/0.95  --bmc1_dump_clauses_tptp                false
% 0.96/0.95  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.95  --bmc1_dump_file                        -
% 0.96/0.95  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.95  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.95  --bmc1_ucm_extend_mode                  1
% 0.96/0.95  --bmc1_ucm_init_mode                    2
% 0.96/0.95  --bmc1_ucm_cone_mode                    none
% 0.96/0.95  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.95  --bmc1_ucm_relax_model                  4
% 0.96/0.95  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.95  --bmc1_ucm_layered_model                none
% 0.96/0.95  --bmc1_ucm_max_lemma_size               10
% 0.96/0.95  
% 0.96/0.95  ------ AIG Options
% 0.96/0.95  
% 0.96/0.95  --aig_mode                              false
% 0.96/0.95  
% 0.96/0.95  ------ Instantiation Options
% 0.96/0.95  
% 0.96/0.95  --instantiation_flag                    true
% 0.96/0.95  --inst_sos_flag                         false
% 0.96/0.95  --inst_sos_phase                        true
% 0.96/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.95  --inst_lit_sel_side                     none
% 0.96/0.95  --inst_solver_per_active                1400
% 0.96/0.95  --inst_solver_calls_frac                1.
% 0.96/0.95  --inst_passive_queue_type               priority_queues
% 0.96/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.95  --inst_passive_queues_freq              [25;2]
% 0.96/0.95  --inst_dismatching                      true
% 0.96/0.95  --inst_eager_unprocessed_to_passive     true
% 0.96/0.95  --inst_prop_sim_given                   true
% 0.96/0.95  --inst_prop_sim_new                     false
% 0.96/0.95  --inst_subs_new                         false
% 0.96/0.95  --inst_eq_res_simp                      false
% 0.96/0.95  --inst_subs_given                       false
% 0.96/0.95  --inst_orphan_elimination               true
% 0.96/0.95  --inst_learning_loop_flag               true
% 0.96/0.95  --inst_learning_start                   3000
% 0.96/0.95  --inst_learning_factor                  2
% 0.96/0.95  --inst_start_prop_sim_after_learn       3
% 0.96/0.95  --inst_sel_renew                        solver
% 0.96/0.95  --inst_lit_activity_flag                true
% 0.96/0.95  --inst_restr_to_given                   false
% 0.96/0.95  --inst_activity_threshold               500
% 0.96/0.95  --inst_out_proof                        true
% 0.96/0.95  
% 0.96/0.95  ------ Resolution Options
% 0.96/0.95  
% 0.96/0.95  --resolution_flag                       false
% 0.96/0.95  --res_lit_sel                           adaptive
% 0.96/0.95  --res_lit_sel_side                      none
% 0.96/0.95  --res_ordering                          kbo
% 0.96/0.95  --res_to_prop_solver                    active
% 0.96/0.95  --res_prop_simpl_new                    false
% 0.96/0.95  --res_prop_simpl_given                  true
% 0.96/0.95  --res_passive_queue_type                priority_queues
% 0.96/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.95  --res_passive_queues_freq               [15;5]
% 0.96/0.95  --res_forward_subs                      full
% 0.96/0.95  --res_backward_subs                     full
% 0.96/0.95  --res_forward_subs_resolution           true
% 0.96/0.95  --res_backward_subs_resolution          true
% 0.96/0.95  --res_orphan_elimination                true
% 0.96/0.95  --res_time_limit                        2.
% 0.96/0.95  --res_out_proof                         true
% 0.96/0.95  
% 0.96/0.95  ------ Superposition Options
% 0.96/0.95  
% 0.96/0.95  --superposition_flag                    true
% 0.96/0.95  --sup_passive_queue_type                priority_queues
% 0.96/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.95  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.95  --demod_completeness_check              fast
% 0.96/0.95  --demod_use_ground                      true
% 0.96/0.95  --sup_to_prop_solver                    passive
% 0.96/0.95  --sup_prop_simpl_new                    true
% 0.96/0.95  --sup_prop_simpl_given                  true
% 0.96/0.95  --sup_fun_splitting                     false
% 0.96/0.95  --sup_smt_interval                      50000
% 0.96/0.95  
% 0.96/0.95  ------ Superposition Simplification Setup
% 0.96/0.95  
% 0.96/0.95  --sup_indices_passive                   []
% 0.96/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.95  --sup_full_bw                           [BwDemod]
% 0.96/0.95  --sup_immed_triv                        [TrivRules]
% 0.96/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.95  --sup_immed_bw_main                     []
% 0.96/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.95  
% 0.96/0.95  ------ Combination Options
% 0.96/0.95  
% 0.96/0.95  --comb_res_mult                         3
% 0.96/0.95  --comb_sup_mult                         2
% 0.96/0.95  --comb_inst_mult                        10
% 0.96/0.95  
% 0.96/0.95  ------ Debug Options
% 0.96/0.95  
% 0.96/0.95  --dbg_backtrace                         false
% 0.96/0.95  --dbg_dump_prop_clauses                 false
% 0.96/0.95  --dbg_dump_prop_clauses_file            -
% 0.96/0.95  --dbg_out_stat                          false
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  ------ Proving...
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  % SZS status Theorem for theBenchmark.p
% 0.96/0.95  
% 0.96/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 0.96/0.95  
% 0.96/0.95  fof(f2,axiom,(
% 0.96/0.95    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattices(X0,X1,X2) <=> (k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0))))))),
% 0.96/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.95  
% 0.96/0.95  fof(f10,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.96/0.95    inference(ennf_transformation,[],[f2])).
% 0.96/0.95  
% 0.96/0.95  fof(f11,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.96/0.95    inference(flattening,[],[f10])).
% 0.96/0.95  
% 0.96/0.95  fof(f18,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | (k2_lattices(X0,X2,X1) != k5_lattices(X0) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k1_lattices(X0,X2,X1) != k6_lattices(X0) | k1_lattices(X0,X1,X2) != k6_lattices(X0))) & ((k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.96/0.95    inference(nnf_transformation,[],[f11])).
% 0.96/0.95  
% 0.96/0.95  fof(f19,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | k2_lattices(X0,X2,X1) != k5_lattices(X0) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k1_lattices(X0,X2,X1) != k6_lattices(X0) | k1_lattices(X0,X1,X2) != k6_lattices(X0)) & ((k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.96/0.95    inference(flattening,[],[f18])).
% 0.96/0.95  
% 0.96/0.95  fof(f31,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (r2_lattices(X0,X1,X2) | k2_lattices(X0,X2,X1) != k5_lattices(X0) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k1_lattices(X0,X2,X1) != k6_lattices(X0) | k1_lattices(X0,X1,X2) != k6_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f19])).
% 0.96/0.95  
% 0.96/0.95  fof(f5,conjecture,(
% 0.96/0.95    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.96/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.95  
% 0.96/0.95  fof(f6,negated_conjecture,(
% 0.96/0.95    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.96/0.95    inference(negated_conjecture,[],[f5])).
% 0.96/0.95  
% 0.96/0.95  fof(f16,plain,(
% 0.96/0.95    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.96/0.95    inference(ennf_transformation,[],[f6])).
% 0.96/0.95  
% 0.96/0.95  fof(f17,plain,(
% 0.96/0.95    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.96/0.95    inference(flattening,[],[f16])).
% 0.96/0.95  
% 0.96/0.95  fof(f22,plain,(
% 0.96/0.95    ( ! [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) => (k7_lattices(X0,k7_lattices(X0,sK1)) != sK1 & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 0.96/0.95    introduced(choice_axiom,[])).
% 0.96/0.95  
% 0.96/0.95  fof(f21,plain,(
% 0.96/0.95    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k7_lattices(sK0,k7_lattices(sK0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.96/0.95    introduced(choice_axiom,[])).
% 0.96/0.95  
% 0.96/0.95  fof(f23,plain,(
% 0.96/0.95    (k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1 & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.96/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22,f21])).
% 0.96/0.95  
% 0.96/0.95  fof(f35,plain,(
% 0.96/0.95    ~v2_struct_0(sK0)),
% 0.96/0.95    inference(cnf_transformation,[],[f23])).
% 0.96/0.95  
% 0.96/0.95  fof(f38,plain,(
% 0.96/0.95    l3_lattices(sK0)),
% 0.96/0.95    inference(cnf_transformation,[],[f23])).
% 0.96/0.95  
% 0.96/0.95  fof(f3,axiom,(
% 0.96/0.95    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ((l3_lattices(X0) & v16_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1))))))),
% 0.96/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.95  
% 0.96/0.95  fof(f12,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : ((! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.96/0.95    inference(ennf_transformation,[],[f3])).
% 0.96/0.95  
% 0.96/0.95  fof(f13,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : (! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.96/0.95    inference(flattening,[],[f12])).
% 0.96/0.95  
% 0.96/0.95  fof(f20,plain,(
% 0.96/0.95    ! [X0] : (! [X1] : (! [X2] : (((k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1)) & (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.96/0.95    inference(nnf_transformation,[],[f13])).
% 0.96/0.95  
% 0.96/0.95  fof(f33,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f20])).
% 0.96/0.95  
% 0.96/0.95  fof(f1,axiom,(
% 0.96/0.95    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.96/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.95  
% 0.96/0.95  fof(f7,plain,(
% 0.96/0.95    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.96/0.95    inference(pure_predicate_removal,[],[f1])).
% 0.96/0.95  
% 0.96/0.95  fof(f8,plain,(
% 0.96/0.95    ! [X0] : (((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.96/0.95    inference(ennf_transformation,[],[f7])).
% 0.96/0.95  
% 0.96/0.95  fof(f9,plain,(
% 0.96/0.95    ! [X0] : ((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.96/0.95    inference(flattening,[],[f8])).
% 0.96/0.95  
% 0.96/0.95  fof(f26,plain,(
% 0.96/0.95    ( ! [X0] : (v16_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f9])).
% 0.96/0.95  
% 0.96/0.95  fof(f37,plain,(
% 0.96/0.95    v17_lattices(sK0)),
% 0.96/0.95    inference(cnf_transformation,[],[f23])).
% 0.96/0.95  
% 0.96/0.95  fof(f36,plain,(
% 0.96/0.95    v10_lattices(sK0)),
% 0.96/0.95    inference(cnf_transformation,[],[f23])).
% 0.96/0.95  
% 0.96/0.95  fof(f25,plain,(
% 0.96/0.95    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f9])).
% 0.96/0.95  
% 0.96/0.95  fof(f4,axiom,(
% 0.96/0.95    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.96/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.95  
% 0.96/0.95  fof(f14,plain,(
% 0.96/0.95    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.96/0.95    inference(ennf_transformation,[],[f4])).
% 0.96/0.95  
% 0.96/0.95  fof(f15,plain,(
% 0.96/0.95    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.96/0.95    inference(flattening,[],[f14])).
% 0.96/0.95  
% 0.96/0.95  fof(f34,plain,(
% 0.96/0.95    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f15])).
% 0.96/0.95  
% 0.96/0.95  fof(f32,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f20])).
% 0.96/0.95  
% 0.96/0.95  fof(f41,plain,(
% 0.96/0.95    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(equality_resolution,[],[f32])).
% 0.96/0.95  
% 0.96/0.95  fof(f27,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k6_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f19])).
% 0.96/0.95  
% 0.96/0.95  fof(f28,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (k1_lattices(X0,X2,X1) = k6_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f19])).
% 0.96/0.95  
% 0.96/0.95  fof(f29,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k5_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f19])).
% 0.96/0.95  
% 0.96/0.95  fof(f30,plain,(
% 0.96/0.95    ( ! [X2,X0,X1] : (k2_lattices(X0,X2,X1) = k5_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.96/0.95    inference(cnf_transformation,[],[f19])).
% 0.96/0.95  
% 0.96/0.95  fof(f40,plain,(
% 0.96/0.95    k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1),
% 0.96/0.95    inference(cnf_transformation,[],[f23])).
% 0.96/0.95  
% 0.96/0.95  fof(f39,plain,(
% 0.96/0.95    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.96/0.95    inference(cnf_transformation,[],[f23])).
% 0.96/0.95  
% 0.96/0.95  cnf(c_3,plain,
% 0.96/0.95      ( r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | k1_lattices(X0,X2,X1) != k6_lattices(X0)
% 0.96/0.95      | k1_lattices(X0,X1,X2) != k6_lattices(X0)
% 0.96/0.95      | k2_lattices(X0,X2,X1) != k5_lattices(X0)
% 0.96/0.95      | k2_lattices(X0,X1,X2) != k5_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f31]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_16,negated_conjecture,
% 0.96/0.95      ( ~ v2_struct_0(sK0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f35]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_335,plain,
% 0.96/0.95      ( r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | k1_lattices(X0,X2,X1) != k6_lattices(X0)
% 0.96/0.95      | k1_lattices(X0,X1,X2) != k6_lattices(X0)
% 0.96/0.95      | k2_lattices(X0,X2,X1) != k5_lattices(X0)
% 0.96/0.95      | k2_lattices(X0,X1,X2) != k5_lattices(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_336,plain,
% 0.96/0.95      ( r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X1,X0) != k5_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_335]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_13,negated_conjecture,
% 0.96/0.95      ( l3_lattices(sK0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f38]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_340,plain,
% 0.96/0.95      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | r2_lattices(sK0,X0,X1)
% 0.96/0.95      | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X1,X0) != k5_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_336,c_13]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_341,plain,
% 0.96/0.95      ( r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X1,X0) != k5_lattices(sK0) ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_340]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_8,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ v10_lattices(X0)
% 0.96/0.95      | ~ v11_lattices(X0)
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | ~ v16_lattices(X0)
% 0.96/0.95      | k7_lattices(X0,X2) = X1 ),
% 0.96/0.95      inference(cnf_transformation,[],[f33]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_0,plain,
% 0.96/0.95      ( ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | ~ v17_lattices(X0)
% 0.96/0.95      | v16_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f26]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_14,negated_conjecture,
% 0.96/0.95      ( v17_lattices(sK0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f37]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_178,plain,
% 0.96/0.95      ( ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | v16_lattices(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_179,plain,
% 0.96/0.95      ( ~ l3_lattices(sK0) | v2_struct_0(sK0) | v16_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_178]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_47,plain,
% 0.96/0.95      ( ~ l3_lattices(sK0)
% 0.96/0.95      | v2_struct_0(sK0)
% 0.96/0.95      | ~ v17_lattices(sK0)
% 0.96/0.95      | v16_lattices(sK0) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_0]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_181,plain,
% 0.96/0.95      ( v16_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_179,c_16,c_14,c_13,c_47]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_214,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ v10_lattices(X0)
% 0.96/0.95      | ~ v11_lattices(X0)
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | k7_lattices(X0,X2) = X1
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_8,c_181]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_215,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ v10_lattices(sK0)
% 0.96/0.95      | ~ v11_lattices(sK0)
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | v2_struct_0(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1) = X0 ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_214]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_15,negated_conjecture,
% 0.96/0.95      ( v10_lattices(sK0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f36]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_1,plain,
% 0.96/0.95      ( v11_lattices(X0)
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | ~ v17_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f25]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_44,plain,
% 0.96/0.95      ( v11_lattices(sK0)
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | v2_struct_0(sK0)
% 0.96/0.95      | ~ v17_lattices(sK0) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_219,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | k7_lattices(sK0,X1) = X0 ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_215,c_16,c_15,c_14,c_13,c_44]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_220,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k7_lattices(sK0,X1) = X0 ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_219]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_425,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X1,X0) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X0,X1) != k6_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X1,X0) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X0,X1) != k5_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1) = X0 ),
% 0.96/0.95      inference(resolution,[status(thm)],[c_341,c_220]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_606,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X1_44,X0_44) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X0_44,X1_44) != k5_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X1_44,X0_44) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X0_44,X1_44) != k6_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1_44) = X0_44 ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_425]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_822,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) != k5_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) != k6_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,k7_lattices(sK0,X0_44)) = X0_44 ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_606]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_824,plain,
% 0.96/0.95      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k5_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) != k5_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k6_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) != k6_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_822]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_10,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.96/0.95      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 0.96/0.95      | ~ l3_lattices(X1)
% 0.96/0.95      | v2_struct_0(X1) ),
% 0.96/0.95      inference(cnf_transformation,[],[f34]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_368,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.96/0.95      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 0.96/0.95      | ~ l3_lattices(X1)
% 0.96/0.95      | sK0 != X1 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_369,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | ~ l3_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_368]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_373,plain,
% 0.96/0.95      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_369,c_13]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_374,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_373]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_9,plain,
% 0.96/0.95      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
% 0.96/0.95      | ~ v10_lattices(X0)
% 0.96/0.95      | ~ v11_lattices(X0)
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | ~ v16_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f41]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_193,plain,
% 0.96/0.95      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
% 0.96/0.95      | ~ v10_lattices(X0)
% 0.96/0.95      | ~ v11_lattices(X0)
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_181]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_194,plain,
% 0.96/0.95      ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | ~ v10_lattices(sK0)
% 0.96/0.95      | ~ v11_lattices(sK0)
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | v2_struct_0(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_193]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_198,plain,
% 0.96/0.95      ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_194,c_16,c_15,c_14,c_13,c_44]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_416,plain,
% 0.96/0.95      ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 0.96/0.95      inference(backward_subsumption_resolution,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_374,c_198]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_7,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | k1_lattices(X0,X1,X2) = k6_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f27]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_247,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | k1_lattices(X0,X1,X2) = k6_lattices(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_248,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X0,X1) = k6_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_247]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_252,plain,
% 0.96/0.95      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | k1_lattices(sK0,X0,X1) = k6_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_248,c_13]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_253,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X0,X1) = k6_lattices(sK0) ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_252]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_505,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 0.96/0.95      | X2 != X1
% 0.96/0.95      | k1_lattices(sK0,X0,X2) = k6_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1) != X0
% 0.96/0.95      | sK0 != sK0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_416,c_253]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_506,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,k7_lattices(sK0,X0),X0) = k6_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_505]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_510,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,k7_lattices(sK0,X0),X0) = k6_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_506,c_13,c_369]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_602,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) = k6_lattices(sK0) ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_510]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_646,plain,
% 0.96/0.95      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k6_lattices(sK0) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_602]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_6,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | k1_lattices(X0,X2,X1) = k6_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f28]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_271,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | k1_lattices(X0,X2,X1) = k6_lattices(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_272,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | k1_lattices(sK0,X1,X0) = k6_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_271]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_274,plain,
% 0.96/0.95      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | k1_lattices(sK0,X1,X0) = k6_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_272,c_13]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_275,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X1,X0) = k6_lattices(sK0) ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_274]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_487,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 0.96/0.95      | X2 != X1
% 0.96/0.95      | k1_lattices(sK0,X2,X0) = k6_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1) != X0
% 0.96/0.95      | sK0 != sK0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_416,c_275]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_488,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_487]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_492,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_488,c_13,c_369]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_603,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) = k6_lattices(sK0) ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_492]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_643,plain,
% 0.96/0.95      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 0.96/0.95      | k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k6_lattices(sK0) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_603]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_5,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | k2_lattices(X0,X1,X2) = k5_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f29]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_291,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | k2_lattices(X0,X1,X2) = k5_lattices(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_292,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_291]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_296,plain,
% 0.96/0.95      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_292,c_13]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_297,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_296]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_469,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 0.96/0.95      | X2 != X1
% 0.96/0.95      | k2_lattices(sK0,X0,X2) = k5_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1) != X0
% 0.96/0.95      | sK0 != sK0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_416,c_297]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_470,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_469]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_474,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_470,c_13,c_369]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_604,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,k7_lattices(sK0,X0_44),X0_44) = k5_lattices(sK0) ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_474]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_640,plain,
% 0.96/0.95      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k5_lattices(sK0) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_604]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_4,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | v2_struct_0(X0)
% 0.96/0.95      | k2_lattices(X0,X2,X1) = k5_lattices(X0) ),
% 0.96/0.95      inference(cnf_transformation,[],[f30]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_315,plain,
% 0.96/0.95      ( ~ r2_lattices(X0,X1,X2)
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.96/0.95      | ~ l3_lattices(X0)
% 0.96/0.95      | k2_lattices(X0,X2,X1) = k5_lattices(X0)
% 0.96/0.95      | sK0 != X0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_316,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ l3_lattices(sK0)
% 0.96/0.95      | k2_lattices(sK0,X1,X0) = k5_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_315]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_318,plain,
% 0.96/0.95      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | k2_lattices(sK0,X1,X0) = k5_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_316,c_13]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_319,plain,
% 0.96/0.95      ( ~ r2_lattices(sK0,X0,X1)
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X1,X0) = k5_lattices(sK0) ),
% 0.96/0.95      inference(renaming,[status(thm)],[c_318]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_451,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 0.96/0.95      | X2 != X1
% 0.96/0.95      | k2_lattices(sK0,X2,X0) = k5_lattices(sK0)
% 0.96/0.95      | k7_lattices(sK0,X1) != X0
% 0.96/0.95      | sK0 != sK0 ),
% 0.96/0.95      inference(resolution_lifted,[status(thm)],[c_416,c_319]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_452,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X0,k7_lattices(sK0,X0)) = k5_lattices(sK0) ),
% 0.96/0.95      inference(unflattening,[status(thm)],[c_451]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_456,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X0,k7_lattices(sK0,X0)) = k5_lattices(sK0) ),
% 0.96/0.95      inference(global_propositional_subsumption,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_452,c_13,c_369]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_605,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,X0_44,k7_lattices(sK0,X0_44)) = k5_lattices(sK0) ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_456]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_637,plain,
% 0.96/0.95      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 0.96/0.95      | k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k5_lattices(sK0) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_605]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_607,plain,
% 0.96/0.95      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 0.96/0.95      | m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0)) ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_374]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_631,plain,
% 0.96/0.95      ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 0.96/0.95      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 0.96/0.95      inference(instantiation,[status(thm)],[c_607]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_11,negated_conjecture,
% 0.96/0.95      ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1 ),
% 0.96/0.95      inference(cnf_transformation,[],[f40]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_609,negated_conjecture,
% 0.96/0.95      ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1 ),
% 0.96/0.95      inference(subtyping,[status(esa)],[c_11]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(c_12,negated_conjecture,
% 0.96/0.95      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 0.96/0.95      inference(cnf_transformation,[],[f39]) ).
% 0.96/0.95  
% 0.96/0.95  cnf(contradiction,plain,
% 0.96/0.95      ( $false ),
% 0.96/0.95      inference(minisat,
% 0.96/0.95                [status(thm)],
% 0.96/0.95                [c_824,c_646,c_643,c_640,c_637,c_631,c_609,c_12]) ).
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 0.96/0.95  
% 0.96/0.95  ------                               Statistics
% 0.96/0.95  
% 0.96/0.95  ------ General
% 0.96/0.95  
% 0.96/0.95  abstr_ref_over_cycles:                  0
% 0.96/0.95  abstr_ref_under_cycles:                 0
% 0.96/0.95  gc_basic_clause_elim:                   0
% 0.96/0.95  forced_gc_time:                         0
% 0.96/0.95  parsing_time:                           0.009
% 0.96/0.95  unif_index_cands_time:                  0.
% 0.96/0.95  unif_index_add_time:                    0.
% 0.96/0.95  orderings_time:                         0.
% 0.96/0.95  out_proof_time:                         0.044
% 0.96/0.95  total_time:                             0.089
% 0.96/0.95  num_of_symbols:                         49
% 0.96/0.95  num_of_terms:                           588
% 0.96/0.95  
% 0.96/0.95  ------ Preprocessing
% 0.96/0.95  
% 0.96/0.95  num_of_splits:                          0
% 0.96/0.95  num_of_split_atoms:                     0
% 0.96/0.95  num_of_reused_defs:                     0
% 0.96/0.95  num_eq_ax_congr_red:                    19
% 0.96/0.95  num_of_sem_filtered_clauses:            1
% 0.96/0.95  num_of_subtypes:                        5
% 0.96/0.95  monotx_restored_types:                  0
% 0.96/0.95  sat_num_of_epr_types:                   0
% 0.96/0.95  sat_num_of_non_cyclic_types:            0
% 0.96/0.95  sat_guarded_non_collapsed_types:        1
% 0.96/0.95  num_pure_diseq_elim:                    0
% 0.96/0.95  simp_replaced_by:                       0
% 0.96/0.95  res_preprocessed:                       61
% 0.96/0.95  prep_upred:                             0
% 0.96/0.95  prep_unflattend:                        20
% 0.96/0.95  smt_new_axioms:                         0
% 0.96/0.95  pred_elim_cands:                        1
% 0.96/0.95  pred_elim:                              7
% 0.96/0.95  pred_elim_cl:                           8
% 0.96/0.95  pred_elim_cycles:                       9
% 0.96/0.95  merged_defs:                            0
% 0.96/0.95  merged_defs_ncl:                        0
% 0.96/0.95  bin_hyper_res:                          0
% 0.96/0.95  prep_cycles:                            4
% 0.96/0.95  pred_elim_time:                         0.007
% 0.96/0.95  splitting_time:                         0.
% 0.96/0.95  sem_filter_time:                        0.
% 0.96/0.95  monotx_time:                            0.
% 0.96/0.95  subtype_inf_time:                       0.
% 0.96/0.95  
% 0.96/0.95  ------ Problem properties
% 0.96/0.95  
% 0.96/0.95  clauses:                                8
% 0.96/0.95  conjectures:                            2
% 0.96/0.95  epr:                                    0
% 0.96/0.95  horn:                                   8
% 0.96/0.95  ground:                                 2
% 0.96/0.95  unary:                                  2
% 0.96/0.95  binary:                                 5
% 0.96/0.95  lits:                                   19
% 0.96/0.95  lits_eq:                                10
% 0.96/0.95  fd_pure:                                0
% 0.96/0.95  fd_pseudo:                              0
% 0.96/0.95  fd_cond:                                0
% 0.96/0.95  fd_pseudo_cond:                         1
% 0.96/0.95  ac_symbols:                             0
% 0.96/0.95  
% 0.96/0.95  ------ Propositional Solver
% 0.96/0.95  
% 0.96/0.95  prop_solver_calls:                      22
% 0.96/0.95  prop_fast_solver_calls:                 457
% 0.96/0.95  smt_solver_calls:                       0
% 0.96/0.95  smt_fast_solver_calls:                  0
% 0.96/0.95  prop_num_of_clauses:                    197
% 0.96/0.95  prop_preprocess_simplified:             1500
% 0.96/0.95  prop_fo_subsumed:                       22
% 0.96/0.95  prop_solver_time:                       0.
% 0.96/0.95  smt_solver_time:                        0.
% 0.96/0.95  smt_fast_solver_time:                   0.
% 0.96/0.95  prop_fast_solver_time:                  0.
% 0.96/0.95  prop_unsat_core_time:                   0.
% 0.96/0.95  
% 0.96/0.95  ------ QBF
% 0.96/0.95  
% 0.96/0.95  qbf_q_res:                              0
% 0.96/0.95  qbf_num_tautologies:                    0
% 0.96/0.95  qbf_prep_cycles:                        0
% 0.96/0.95  
% 0.96/0.95  ------ BMC1
% 0.96/0.95  
% 0.96/0.95  bmc1_current_bound:                     -1
% 0.96/0.95  bmc1_last_solved_bound:                 -1
% 0.96/0.95  bmc1_unsat_core_size:                   -1
% 0.96/0.95  bmc1_unsat_core_parents_size:           -1
% 0.96/0.95  bmc1_merge_next_fun:                    0
% 0.96/0.95  bmc1_unsat_core_clauses_time:           0.
% 0.96/0.95  
% 0.96/0.95  ------ Instantiation
% 0.96/0.95  
% 0.96/0.95  inst_num_of_clauses:                    18
% 0.96/0.95  inst_num_in_passive:                    10
% 0.96/0.95  inst_num_in_active:                     7
% 0.96/0.95  inst_num_in_unprocessed:                0
% 0.96/0.95  inst_num_of_loops:                      8
% 0.96/0.95  inst_num_of_learning_restarts:          0
% 0.96/0.95  inst_num_moves_active_passive:          0
% 0.96/0.95  inst_lit_activity:                      0
% 0.96/0.95  inst_lit_activity_moves:                0
% 0.96/0.95  inst_num_tautologies:                   0
% 0.96/0.95  inst_num_prop_implied:                  0
% 0.96/0.95  inst_num_existing_simplified:           0
% 0.96/0.95  inst_num_eq_res_simplified:             0
% 0.96/0.95  inst_num_child_elim:                    0
% 0.96/0.95  inst_num_of_dismatching_blockings:      0
% 0.96/0.95  inst_num_of_non_proper_insts:           1
% 0.96/0.95  inst_num_of_duplicates:                 0
% 0.96/0.95  inst_inst_num_from_inst_to_res:         0
% 0.96/0.95  inst_dismatching_checking_time:         0.
% 0.96/0.95  
% 0.96/0.95  ------ Resolution
% 0.96/0.95  
% 0.96/0.95  res_num_of_clauses:                     0
% 0.96/0.95  res_num_in_passive:                     0
% 0.96/0.95  res_num_in_active:                      0
% 0.96/0.95  res_num_of_loops:                       65
% 0.96/0.95  res_forward_subset_subsumed:            0
% 0.96/0.95  res_backward_subset_subsumed:           0
% 0.96/0.95  res_forward_subsumed:                   0
% 0.96/0.95  res_backward_subsumed:                  0
% 0.96/0.95  res_forward_subsumption_resolution:     0
% 0.96/0.95  res_backward_subsumption_resolution:    1
% 0.96/0.95  res_clause_to_clause_subsumption:       27
% 0.96/0.95  res_orphan_elimination:                 0
% 0.96/0.95  res_tautology_del:                      6
% 0.96/0.95  res_num_eq_res_simplified:              0
% 0.96/0.95  res_num_sel_changes:                    0
% 0.96/0.95  res_moves_from_active_to_pass:          0
% 0.96/0.95  
% 0.96/0.95  ------ Superposition
% 0.96/0.95  
% 0.96/0.95  sup_time_total:                         0.
% 0.96/0.95  sup_time_generating:                    0.
% 0.96/0.95  sup_time_sim_full:                      0.
% 0.96/0.95  sup_time_sim_immed:                     0.
% 0.96/0.95  
% 0.96/0.95  sup_num_of_clauses:                     8
% 0.96/0.95  sup_num_in_active:                      0
% 0.96/0.95  sup_num_in_passive:                     8
% 0.96/0.95  sup_num_of_loops:                       0
% 0.96/0.95  sup_fw_superposition:                   0
% 0.96/0.95  sup_bw_superposition:                   0
% 0.96/0.95  sup_immediate_simplified:               0
% 0.96/0.95  sup_given_eliminated:                   0
% 0.96/0.95  comparisons_done:                       0
% 0.96/0.95  comparisons_avoided:                    0
% 0.96/0.95  
% 0.96/0.95  ------ Simplifications
% 0.96/0.95  
% 0.96/0.95  
% 0.96/0.95  sim_fw_subset_subsumed:                 0
% 0.96/0.95  sim_bw_subset_subsumed:                 0
% 0.96/0.95  sim_fw_subsumed:                        0
% 0.96/0.95  sim_bw_subsumed:                        0
% 0.96/0.95  sim_fw_subsumption_res:                 0
% 0.96/0.95  sim_bw_subsumption_res:                 0
% 0.96/0.95  sim_tautology_del:                      0
% 0.96/0.95  sim_eq_tautology_del:                   0
% 0.96/0.95  sim_eq_res_simp:                        0
% 0.96/0.95  sim_fw_demodulated:                     0
% 0.96/0.95  sim_bw_demodulated:                     0
% 0.96/0.95  sim_light_normalised:                   0
% 0.96/0.95  sim_joinable_taut:                      0
% 0.96/0.95  sim_joinable_simp:                      0
% 0.96/0.95  sim_ac_normalised:                      0
% 0.96/0.95  sim_smt_subsumption:                    0
% 0.96/0.95  
%------------------------------------------------------------------------------

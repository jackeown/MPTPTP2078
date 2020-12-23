%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:09 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 0.89s
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

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:18 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 370 expanded)
%              Number of clauses        :   45 (  78 expanded)
%              Number of leaves         :   10 (  92 expanded)
%              Depth                    :   21
%              Number of atoms          :  463 (1995 expanded)
%              Number of equality atoms :   66 (  66 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f15,plain,(
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
    inference(flattening,[],[f15])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k5_lattices(X0),sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_lattices(sK1,k5_lattices(sK1),X1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v13_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r3_lattices(sK1,k5_lattices(sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v13_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33,f32])).

fof(f51,plain,(
    v13_lattices(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ~ r3_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,negated_conjecture,
    ( v13_lattices(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_39,plain,
    ( l1_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_42,plain,
    ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_19,c_16,c_39,c_42])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),X0_45) = k5_lattices(sK1) ),
    inference(subtyping,[status(esa)],[c_407])).

cnf(c_575,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),sK2) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_12,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_236,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_237,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | v9_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_64,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | v9_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_239,plain,
    ( v9_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_237,c_19,c_18,c_16,c_64])).

cnf(c_349,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_239])).

cnf(c_350,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_61,plain,
    ( v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_lattices(sK1,X0,X1)
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_19,c_18,c_16,c_61])).

cnf(c_355,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_14,negated_conjecture,
    ( ~ r3_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_214,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_215,plain,
    ( v6_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_58,plain,
    ( v6_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_217,plain,
    ( v6_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_215,c_19,c_18,c_16,c_58])).

cnf(c_277,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_217])).

cnf(c_278,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v9_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_282,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_19,c_18,c_16,c_61,c_64])).

cnf(c_312,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k5_lattices(sK1) != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_282])).

cnf(c_313,plain,
    ( ~ r1_lattices(sK1,k5_lattices(sK1),sK2)
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_315,plain,
    ( ~ r1_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_19,c_16,c_15,c_39,c_42])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_lattices(sK1,X1,X0) != X1
    | k5_lattices(sK1) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_315])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_19,c_16,c_15,c_39,c_42])).

cnf(c_562,plain,
    ( k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_575,c_562,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:05:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.75/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.75/0.98  
% 0.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.75/0.98  
% 0.75/0.98  ------  iProver source info
% 0.75/0.98  
% 0.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.75/0.98  git: non_committed_changes: false
% 0.75/0.98  git: last_make_outside_of_git: false
% 0.75/0.98  
% 0.75/0.98  ------ 
% 0.75/0.98  
% 0.75/0.98  ------ Input Options
% 0.75/0.98  
% 0.75/0.98  --out_options                           all
% 0.75/0.98  --tptp_safe_out                         true
% 0.75/0.98  --problem_path                          ""
% 0.75/0.98  --include_path                          ""
% 0.75/0.98  --clausifier                            res/vclausify_rel
% 0.75/0.98  --clausifier_options                    --mode clausify
% 0.75/0.98  --stdin                                 false
% 0.75/0.98  --stats_out                             all
% 0.75/0.98  
% 0.75/0.98  ------ General Options
% 0.75/0.98  
% 0.75/0.98  --fof                                   false
% 0.75/0.98  --time_out_real                         305.
% 0.75/0.98  --time_out_virtual                      -1.
% 0.75/0.98  --symbol_type_check                     false
% 0.75/0.98  --clausify_out                          false
% 0.75/0.98  --sig_cnt_out                           false
% 0.75/0.98  --trig_cnt_out                          false
% 0.75/0.98  --trig_cnt_out_tolerance                1.
% 0.75/0.98  --trig_cnt_out_sk_spl                   false
% 0.75/0.98  --abstr_cl_out                          false
% 0.75/0.98  
% 0.75/0.98  ------ Global Options
% 0.75/0.98  
% 0.75/0.98  --schedule                              default
% 0.75/0.98  --add_important_lit                     false
% 0.75/0.98  --prop_solver_per_cl                    1000
% 0.75/0.98  --min_unsat_core                        false
% 0.75/0.98  --soft_assumptions                      false
% 0.75/0.98  --soft_lemma_size                       3
% 0.75/0.98  --prop_impl_unit_size                   0
% 0.75/0.98  --prop_impl_unit                        []
% 0.75/0.98  --share_sel_clauses                     true
% 0.75/0.98  --reset_solvers                         false
% 0.75/0.98  --bc_imp_inh                            [conj_cone]
% 0.75/0.98  --conj_cone_tolerance                   3.
% 0.75/0.98  --extra_neg_conj                        none
% 0.75/0.98  --large_theory_mode                     true
% 0.75/0.98  --prolific_symb_bound                   200
% 0.75/0.98  --lt_threshold                          2000
% 0.75/0.98  --clause_weak_htbl                      true
% 0.75/0.98  --gc_record_bc_elim                     false
% 0.75/0.98  
% 0.75/0.98  ------ Preprocessing Options
% 0.75/0.98  
% 0.75/0.98  --preprocessing_flag                    true
% 0.75/0.98  --time_out_prep_mult                    0.1
% 0.75/0.98  --splitting_mode                        input
% 0.75/0.98  --splitting_grd                         true
% 0.75/0.98  --splitting_cvd                         false
% 0.75/0.98  --splitting_cvd_svl                     false
% 0.75/0.98  --splitting_nvd                         32
% 0.75/0.98  --sub_typing                            true
% 0.75/0.98  --prep_gs_sim                           true
% 0.75/0.98  --prep_unflatten                        true
% 0.75/0.98  --prep_res_sim                          true
% 0.75/0.98  --prep_upred                            true
% 0.75/0.98  --prep_sem_filter                       exhaustive
% 0.75/0.98  --prep_sem_filter_out                   false
% 0.75/0.98  --pred_elim                             true
% 0.75/0.98  --res_sim_input                         true
% 0.75/0.98  --eq_ax_congr_red                       true
% 0.75/0.98  --pure_diseq_elim                       true
% 0.75/0.98  --brand_transform                       false
% 0.75/0.98  --non_eq_to_eq                          false
% 0.75/0.98  --prep_def_merge                        true
% 0.75/0.98  --prep_def_merge_prop_impl              false
% 0.75/0.98  --prep_def_merge_mbd                    true
% 0.75/0.98  --prep_def_merge_tr_red                 false
% 0.75/0.98  --prep_def_merge_tr_cl                  false
% 0.75/0.98  --smt_preprocessing                     true
% 0.75/0.98  --smt_ac_axioms                         fast
% 0.75/0.98  --preprocessed_out                      false
% 0.75/0.98  --preprocessed_stats                    false
% 0.75/0.98  
% 0.75/0.98  ------ Abstraction refinement Options
% 0.75/0.98  
% 0.75/0.98  --abstr_ref                             []
% 0.75/0.98  --abstr_ref_prep                        false
% 0.75/0.98  --abstr_ref_until_sat                   false
% 0.75/0.98  --abstr_ref_sig_restrict                funpre
% 0.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.75/0.98  --abstr_ref_under                       []
% 0.75/0.98  
% 0.75/0.98  ------ SAT Options
% 0.75/0.98  
% 0.75/0.98  --sat_mode                              false
% 0.75/0.98  --sat_fm_restart_options                ""
% 0.75/0.98  --sat_gr_def                            false
% 0.75/0.98  --sat_epr_types                         true
% 0.75/0.98  --sat_non_cyclic_types                  false
% 0.75/0.98  --sat_finite_models                     false
% 0.75/0.98  --sat_fm_lemmas                         false
% 0.75/0.98  --sat_fm_prep                           false
% 0.75/0.98  --sat_fm_uc_incr                        true
% 0.75/0.98  --sat_out_model                         small
% 0.75/0.98  --sat_out_clauses                       false
% 0.75/0.98  
% 0.75/0.98  ------ QBF Options
% 0.75/0.98  
% 0.75/0.98  --qbf_mode                              false
% 0.75/0.98  --qbf_elim_univ                         false
% 0.75/0.98  --qbf_dom_inst                          none
% 0.75/0.98  --qbf_dom_pre_inst                      false
% 0.75/0.98  --qbf_sk_in                             false
% 0.75/0.98  --qbf_pred_elim                         true
% 0.75/0.98  --qbf_split                             512
% 0.75/0.98  
% 0.75/0.98  ------ BMC1 Options
% 0.75/0.98  
% 0.75/0.98  --bmc1_incremental                      false
% 0.75/0.98  --bmc1_axioms                           reachable_all
% 0.75/0.98  --bmc1_min_bound                        0
% 0.75/0.98  --bmc1_max_bound                        -1
% 0.75/0.98  --bmc1_max_bound_default                -1
% 0.75/0.98  --bmc1_symbol_reachability              true
% 0.75/0.98  --bmc1_property_lemmas                  false
% 0.75/0.98  --bmc1_k_induction                      false
% 0.75/0.98  --bmc1_non_equiv_states                 false
% 0.75/0.98  --bmc1_deadlock                         false
% 0.75/0.98  --bmc1_ucm                              false
% 0.75/0.98  --bmc1_add_unsat_core                   none
% 0.75/0.98  --bmc1_unsat_core_children              false
% 0.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.75/0.98  --bmc1_out_stat                         full
% 0.75/0.98  --bmc1_ground_init                      false
% 0.75/0.98  --bmc1_pre_inst_next_state              false
% 0.75/0.98  --bmc1_pre_inst_state                   false
% 0.75/0.98  --bmc1_pre_inst_reach_state             false
% 0.75/0.98  --bmc1_out_unsat_core                   false
% 0.75/0.98  --bmc1_aig_witness_out                  false
% 0.75/0.98  --bmc1_verbose                          false
% 0.75/0.98  --bmc1_dump_clauses_tptp                false
% 0.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.75/0.98  --bmc1_dump_file                        -
% 0.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.75/0.98  --bmc1_ucm_extend_mode                  1
% 0.75/0.98  --bmc1_ucm_init_mode                    2
% 0.75/0.98  --bmc1_ucm_cone_mode                    none
% 0.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.75/0.98  --bmc1_ucm_relax_model                  4
% 0.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.75/0.98  --bmc1_ucm_layered_model                none
% 0.75/0.98  --bmc1_ucm_max_lemma_size               10
% 0.75/0.98  
% 0.75/0.98  ------ AIG Options
% 0.75/0.98  
% 0.75/0.98  --aig_mode                              false
% 0.75/0.98  
% 0.75/0.98  ------ Instantiation Options
% 0.75/0.98  
% 0.75/0.98  --instantiation_flag                    true
% 0.75/0.98  --inst_sos_flag                         false
% 0.75/0.98  --inst_sos_phase                        true
% 0.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.75/0.98  --inst_lit_sel_side                     num_symb
% 0.75/0.98  --inst_solver_per_active                1400
% 0.75/0.98  --inst_solver_calls_frac                1.
% 0.75/0.98  --inst_passive_queue_type               priority_queues
% 0.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.75/0.98  --inst_passive_queues_freq              [25;2]
% 0.75/0.98  --inst_dismatching                      true
% 0.75/0.98  --inst_eager_unprocessed_to_passive     true
% 0.75/0.98  --inst_prop_sim_given                   true
% 0.75/0.98  --inst_prop_sim_new                     false
% 0.75/0.98  --inst_subs_new                         false
% 0.75/0.98  --inst_eq_res_simp                      false
% 0.75/0.98  --inst_subs_given                       false
% 0.75/0.98  --inst_orphan_elimination               true
% 0.75/0.98  --inst_learning_loop_flag               true
% 0.75/0.98  --inst_learning_start                   3000
% 0.75/0.98  --inst_learning_factor                  2
% 0.75/0.98  --inst_start_prop_sim_after_learn       3
% 0.75/0.98  --inst_sel_renew                        solver
% 0.75/0.98  --inst_lit_activity_flag                true
% 0.75/0.98  --inst_restr_to_given                   false
% 0.75/0.98  --inst_activity_threshold               500
% 0.75/0.98  --inst_out_proof                        true
% 0.75/0.98  
% 0.75/0.98  ------ Resolution Options
% 0.75/0.98  
% 0.75/0.98  --resolution_flag                       true
% 0.75/0.98  --res_lit_sel                           adaptive
% 0.75/0.98  --res_lit_sel_side                      none
% 0.75/0.98  --res_ordering                          kbo
% 0.75/0.98  --res_to_prop_solver                    active
% 0.75/0.98  --res_prop_simpl_new                    false
% 0.75/0.98  --res_prop_simpl_given                  true
% 0.75/0.98  --res_passive_queue_type                priority_queues
% 0.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.75/0.98  --res_passive_queues_freq               [15;5]
% 0.75/0.98  --res_forward_subs                      full
% 0.75/0.98  --res_backward_subs                     full
% 0.75/0.98  --res_forward_subs_resolution           true
% 0.75/0.98  --res_backward_subs_resolution          true
% 0.75/0.98  --res_orphan_elimination                true
% 0.75/0.98  --res_time_limit                        2.
% 0.75/0.98  --res_out_proof                         true
% 0.75/0.98  
% 0.75/0.98  ------ Superposition Options
% 0.75/0.98  
% 0.75/0.98  --superposition_flag                    true
% 0.75/0.98  --sup_passive_queue_type                priority_queues
% 0.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.75/0.98  --demod_completeness_check              fast
% 0.75/0.98  --demod_use_ground                      true
% 0.75/0.98  --sup_to_prop_solver                    passive
% 0.75/0.98  --sup_prop_simpl_new                    true
% 0.75/0.98  --sup_prop_simpl_given                  true
% 0.75/0.98  --sup_fun_splitting                     false
% 0.75/0.98  --sup_smt_interval                      50000
% 0.75/0.98  
% 0.75/0.98  ------ Superposition Simplification Setup
% 0.75/0.98  
% 0.75/0.98  --sup_indices_passive                   []
% 0.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.98  --sup_full_bw                           [BwDemod]
% 0.75/0.98  --sup_immed_triv                        [TrivRules]
% 0.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.98  --sup_immed_bw_main                     []
% 0.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/0.98  
% 0.75/0.98  ------ Combination Options
% 0.75/0.98  
% 0.75/0.98  --comb_res_mult                         3
% 0.75/0.98  --comb_sup_mult                         2
% 0.75/0.98  --comb_inst_mult                        10
% 0.75/0.98  
% 0.75/0.98  ------ Debug Options
% 0.75/0.98  
% 0.75/0.98  --dbg_backtrace                         false
% 0.75/0.98  --dbg_dump_prop_clauses                 false
% 0.75/0.98  --dbg_dump_prop_clauses_file            -
% 0.75/0.98  --dbg_out_stat                          false
% 0.75/0.98  ------ Parsing...
% 0.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.75/0.98  
% 0.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.75/0.98  
% 0.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.75/0.98  
% 0.75/0.98  ------ Preprocessing...
% 0.75/0.98  
% 0.75/0.98  % SZS status Theorem for theBenchmark.p
% 0.75/0.98  
% 0.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.75/0.98  
% 0.75/0.98  fof(f2,axiom,(
% 0.75/0.98    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f15,plain,(
% 0.75/0.98    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.75/0.98    inference(ennf_transformation,[],[f2])).
% 0.75/0.98  
% 0.75/0.98  fof(f16,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(flattening,[],[f15])).
% 0.75/0.98  
% 0.75/0.98  fof(f26,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(nnf_transformation,[],[f16])).
% 0.75/0.98  
% 0.75/0.98  fof(f27,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(rectify,[],[f26])).
% 0.75/0.98  
% 0.75/0.98  fof(f28,plain,(
% 0.75/0.98    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 0.75/0.98    introduced(choice_axiom,[])).
% 0.75/0.98  
% 0.75/0.98  fof(f29,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 0.75/0.98  
% 0.75/0.98  fof(f39,plain,(
% 0.75/0.98    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f29])).
% 0.75/0.98  
% 0.75/0.98  fof(f56,plain,(
% 0.75/0.98    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.75/0.98    inference(equality_resolution,[],[f39])).
% 0.75/0.98  
% 0.75/0.98  fof(f7,conjecture,(
% 0.75/0.98    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,k5_lattices(X0),X1)))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f8,negated_conjecture,(
% 0.75/0.98    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,k5_lattices(X0),X1)))),
% 0.75/0.98    inference(negated_conjecture,[],[f7])).
% 0.75/0.98  
% 0.75/0.98  fof(f24,plain,(
% 0.75/0.98    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.75/0.98    inference(ennf_transformation,[],[f8])).
% 0.75/0.98  
% 0.75/0.98  fof(f25,plain,(
% 0.75/0.98    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.75/0.98    inference(flattening,[],[f24])).
% 0.75/0.98  
% 0.75/0.98  fof(f33,plain,(
% 0.75/0.98    ( ! [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (~r3_lattices(X0,k5_lattices(X0),sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 0.75/0.98    introduced(choice_axiom,[])).
% 0.75/0.98  
% 0.75/0.98  fof(f32,plain,(
% 0.75/0.98    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r3_lattices(sK1,k5_lattices(sK1),X1) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v13_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.75/0.98    introduced(choice_axiom,[])).
% 0.75/0.98  
% 0.75/0.98  fof(f34,plain,(
% 0.75/0.98    (~r3_lattices(sK1,k5_lattices(sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v13_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 0.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33,f32])).
% 0.75/0.98  
% 0.75/0.98  fof(f51,plain,(
% 0.75/0.98    v13_lattices(sK1)),
% 0.75/0.98    inference(cnf_transformation,[],[f34])).
% 0.75/0.98  
% 0.75/0.98  fof(f49,plain,(
% 0.75/0.98    ~v2_struct_0(sK1)),
% 0.75/0.98    inference(cnf_transformation,[],[f34])).
% 0.75/0.98  
% 0.75/0.98  fof(f52,plain,(
% 0.75/0.98    l3_lattices(sK1)),
% 0.75/0.98    inference(cnf_transformation,[],[f34])).
% 0.75/0.98  
% 0.75/0.98  fof(f4,axiom,(
% 0.75/0.98    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f9,plain,(
% 0.75/0.98    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.75/0.98    inference(pure_predicate_removal,[],[f4])).
% 0.75/0.98  
% 0.75/0.98  fof(f19,plain,(
% 0.75/0.98    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.75/0.98    inference(ennf_transformation,[],[f9])).
% 0.75/0.98  
% 0.75/0.98  fof(f44,plain,(
% 0.75/0.98    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f19])).
% 0.75/0.98  
% 0.75/0.98  fof(f3,axiom,(
% 0.75/0.98    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f17,plain,(
% 0.75/0.98    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.75/0.98    inference(ennf_transformation,[],[f3])).
% 0.75/0.98  
% 0.75/0.98  fof(f18,plain,(
% 0.75/0.98    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(flattening,[],[f17])).
% 0.75/0.98  
% 0.75/0.98  fof(f43,plain,(
% 0.75/0.98    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f18])).
% 0.75/0.98  
% 0.75/0.98  fof(f6,axiom,(
% 0.75/0.98    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f22,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.75/0.98    inference(ennf_transformation,[],[f6])).
% 0.75/0.98  
% 0.75/0.98  fof(f23,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(flattening,[],[f22])).
% 0.75/0.98  
% 0.75/0.98  fof(f31,plain,(
% 0.75/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(nnf_transformation,[],[f23])).
% 0.75/0.98  
% 0.75/0.98  fof(f48,plain,(
% 0.75/0.98    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f31])).
% 0.75/0.98  
% 0.75/0.98  fof(f1,axiom,(
% 0.75/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f10,plain,(
% 0.75/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.75/0.98    inference(pure_predicate_removal,[],[f1])).
% 0.75/0.98  
% 0.75/0.98  fof(f11,plain,(
% 0.75/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.75/0.98    inference(pure_predicate_removal,[],[f10])).
% 0.75/0.98  
% 0.75/0.98  fof(f12,plain,(
% 0.75/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.75/0.98    inference(pure_predicate_removal,[],[f11])).
% 0.75/0.98  
% 0.75/0.98  fof(f13,plain,(
% 0.75/0.98    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.75/0.98    inference(ennf_transformation,[],[f12])).
% 0.75/0.98  
% 0.75/0.98  fof(f14,plain,(
% 0.75/0.98    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.75/0.98    inference(flattening,[],[f13])).
% 0.75/0.98  
% 0.75/0.98  fof(f38,plain,(
% 0.75/0.98    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f14])).
% 0.75/0.98  
% 0.75/0.98  fof(f50,plain,(
% 0.75/0.98    v10_lattices(sK1)),
% 0.75/0.98    inference(cnf_transformation,[],[f34])).
% 0.75/0.98  
% 0.75/0.98  fof(f37,plain,(
% 0.75/0.98    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f14])).
% 0.75/0.98  
% 0.75/0.98  fof(f54,plain,(
% 0.75/0.98    ~r3_lattices(sK1,k5_lattices(sK1),sK2)),
% 0.75/0.98    inference(cnf_transformation,[],[f34])).
% 0.75/0.98  
% 0.75/0.98  fof(f5,axiom,(
% 0.75/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.75/0.98  
% 0.75/0.98  fof(f20,plain,(
% 0.75/0.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.75/0.98    inference(ennf_transformation,[],[f5])).
% 0.75/0.98  
% 0.75/0.98  fof(f21,plain,(
% 0.75/0.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(flattening,[],[f20])).
% 0.75/0.98  
% 0.75/0.98  fof(f30,plain,(
% 0.75/0.98    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.75/0.98    inference(nnf_transformation,[],[f21])).
% 0.75/0.98  
% 0.75/0.98  fof(f46,plain,(
% 0.75/0.98    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f30])).
% 0.75/0.98  
% 0.75/0.98  fof(f36,plain,(
% 0.75/0.98    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.75/0.98    inference(cnf_transformation,[],[f14])).
% 0.75/0.98  
% 0.75/0.98  fof(f53,plain,(
% 0.75/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.75/0.98    inference(cnf_transformation,[],[f34])).
% 0.75/0.98  
% 0.75/0.98  cnf(c_7,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.75/0.98      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 0.75/0.98      | ~ l1_lattices(X1)
% 0.75/0.98      | ~ v13_lattices(X1)
% 0.75/0.98      | v2_struct_0(X1)
% 0.75/0.98      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 0.75/0.98      inference(cnf_transformation,[],[f56]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_17,negated_conjecture,
% 0.75/0.98      ( v13_lattices(sK1) ),
% 0.75/0.98      inference(cnf_transformation,[],[f51]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_402,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.75/0.98      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 0.75/0.98      | ~ l1_lattices(X1)
% 0.75/0.98      | v2_struct_0(X1)
% 0.75/0.98      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 0.75/0.98      | sK1 != X1 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_403,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.75/0.98      | ~ l1_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1)
% 0.75/0.98      | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_19,negated_conjecture,
% 0.75/0.98      ( ~ v2_struct_0(sK1) ),
% 0.75/0.98      inference(cnf_transformation,[],[f49]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_16,negated_conjecture,
% 0.75/0.98      ( l3_lattices(sK1) ),
% 0.75/0.98      inference(cnf_transformation,[],[f52]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_9,plain,
% 0.75/0.98      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 0.75/0.98      inference(cnf_transformation,[],[f44]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_39,plain,
% 0.75/0.98      ( l1_lattices(sK1) | ~ l3_lattices(sK1) ),
% 0.75/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_8,plain,
% 0.75/0.98      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 0.75/0.98      | ~ l1_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0) ),
% 0.75/0.98      inference(cnf_transformation,[],[f43]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_42,plain,
% 0.75/0.98      ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.75/0.98      | ~ l1_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1) ),
% 0.75/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_407,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_403,c_19,c_16,c_39,c_42]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_561,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 0.75/0.98      | k2_lattices(sK1,k5_lattices(sK1),X0_45) = k5_lattices(sK1) ),
% 0.75/0.98      inference(subtyping,[status(esa)],[c_407]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_575,plain,
% 0.75/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 0.75/0.98      | k2_lattices(sK1,k5_lattices(sK1),sK2) = k5_lattices(sK1) ),
% 0.75/0.98      inference(instantiation,[status(thm)],[c_561]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_12,plain,
% 0.75/0.98      ( r1_lattices(X0,X1,X2)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.75/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.75/0.98      | ~ v8_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | ~ v9_lattices(X0)
% 0.75/0.98      | k2_lattices(X0,X1,X2) != X1 ),
% 0.75/0.98      inference(cnf_transformation,[],[f48]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_0,plain,
% 0.75/0.98      ( ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | ~ v10_lattices(X0)
% 0.75/0.98      | v9_lattices(X0) ),
% 0.75/0.98      inference(cnf_transformation,[],[f38]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_18,negated_conjecture,
% 0.75/0.98      ( v10_lattices(sK1) ),
% 0.75/0.98      inference(cnf_transformation,[],[f50]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_236,plain,
% 0.75/0.98      ( ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | v9_lattices(X0)
% 0.75/0.98      | sK1 != X0 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_237,plain,
% 0.75/0.98      ( ~ l3_lattices(sK1) | v2_struct_0(sK1) | v9_lattices(sK1) ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_236]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_64,plain,
% 0.75/0.98      ( ~ l3_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1)
% 0.75/0.98      | ~ v10_lattices(sK1)
% 0.75/0.98      | v9_lattices(sK1) ),
% 0.75/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_239,plain,
% 0.75/0.98      ( v9_lattices(sK1) ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_237,c_19,c_18,c_16,c_64]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_349,plain,
% 0.75/0.98      ( r1_lattices(X0,X1,X2)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.75/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.75/0.98      | ~ v8_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | k2_lattices(X0,X1,X2) != X1
% 0.75/0.98      | sK1 != X0 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_239]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_350,plain,
% 0.75/0.98      ( r1_lattices(sK1,X0,X1)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | ~ v8_lattices(sK1)
% 0.75/0.98      | ~ l3_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1)
% 0.75/0.98      | k2_lattices(sK1,X0,X1) != X0 ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_349]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_1,plain,
% 0.75/0.98      ( v8_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | ~ v10_lattices(X0) ),
% 0.75/0.98      inference(cnf_transformation,[],[f37]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_61,plain,
% 0.75/0.98      ( v8_lattices(sK1)
% 0.75/0.98      | ~ l3_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1)
% 0.75/0.98      | ~ v10_lattices(sK1) ),
% 0.75/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_354,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | r1_lattices(sK1,X0,X1)
% 0.75/0.98      | k2_lattices(sK1,X0,X1) != X0 ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_350,c_19,c_18,c_16,c_61]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_355,plain,
% 0.75/0.98      ( r1_lattices(sK1,X0,X1)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | k2_lattices(sK1,X0,X1) != X0 ),
% 0.75/0.98      inference(renaming,[status(thm)],[c_354]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_14,negated_conjecture,
% 0.75/0.98      ( ~ r3_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.75/0.98      inference(cnf_transformation,[],[f54]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_10,plain,
% 0.75/0.98      ( ~ r1_lattices(X0,X1,X2)
% 0.75/0.98      | r3_lattices(X0,X1,X2)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.75/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.75/0.98      | ~ v6_lattices(X0)
% 0.75/0.98      | ~ v8_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | ~ v9_lattices(X0) ),
% 0.75/0.98      inference(cnf_transformation,[],[f46]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_2,plain,
% 0.75/0.98      ( v6_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | ~ v10_lattices(X0) ),
% 0.75/0.98      inference(cnf_transformation,[],[f36]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_214,plain,
% 0.75/0.98      ( v6_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | sK1 != X0 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_215,plain,
% 0.75/0.98      ( v6_lattices(sK1) | ~ l3_lattices(sK1) | v2_struct_0(sK1) ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_214]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_58,plain,
% 0.75/0.98      ( v6_lattices(sK1)
% 0.75/0.98      | ~ l3_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1)
% 0.75/0.98      | ~ v10_lattices(sK1) ),
% 0.75/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_217,plain,
% 0.75/0.98      ( v6_lattices(sK1) ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_215,c_19,c_18,c_16,c_58]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_277,plain,
% 0.75/0.98      ( ~ r1_lattices(X0,X1,X2)
% 0.75/0.98      | r3_lattices(X0,X1,X2)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.75/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.75/0.98      | ~ v8_lattices(X0)
% 0.75/0.98      | ~ l3_lattices(X0)
% 0.75/0.98      | v2_struct_0(X0)
% 0.75/0.98      | ~ v9_lattices(X0)
% 0.75/0.98      | sK1 != X0 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_217]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_278,plain,
% 0.75/0.98      ( ~ r1_lattices(sK1,X0,X1)
% 0.75/0.98      | r3_lattices(sK1,X0,X1)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | ~ v8_lattices(sK1)
% 0.75/0.98      | ~ l3_lattices(sK1)
% 0.75/0.98      | v2_struct_0(sK1)
% 0.75/0.98      | ~ v9_lattices(sK1) ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_277]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_282,plain,
% 0.75/0.98      ( ~ r1_lattices(sK1,X0,X1)
% 0.75/0.98      | r3_lattices(sK1,X0,X1)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_278,c_19,c_18,c_16,c_61,c_64]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_312,plain,
% 0.75/0.98      ( ~ r1_lattices(sK1,X0,X1)
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | k5_lattices(sK1) != X0
% 0.75/0.98      | sK2 != X1
% 0.75/0.98      | sK1 != sK1 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_282]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_313,plain,
% 0.75/0.98      ( ~ r1_lattices(sK1,k5_lattices(sK1),sK2)
% 0.75/0.98      | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_312]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_15,negated_conjecture,
% 0.75/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.75/0.98      inference(cnf_transformation,[],[f53]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_315,plain,
% 0.75/0.98      ( ~ r1_lattices(sK1,k5_lattices(sK1),sK2) ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_313,c_19,c_16,c_15,c_39,c_42]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_393,plain,
% 0.75/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.75/0.98      | k2_lattices(sK1,X1,X0) != X1
% 0.75/0.98      | k5_lattices(sK1) != X1
% 0.75/0.98      | sK2 != X0
% 0.75/0.98      | sK1 != sK1 ),
% 0.75/0.98      inference(resolution_lifted,[status(thm)],[c_355,c_315]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_394,plain,
% 0.75/0.98      ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 0.75/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 0.75/0.98      | k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
% 0.75/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_396,plain,
% 0.75/0.98      ( k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
% 0.75/0.98      inference(global_propositional_subsumption,
% 0.75/0.98                [status(thm)],
% 0.75/0.98                [c_394,c_19,c_16,c_15,c_39,c_42]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(c_562,plain,
% 0.75/0.98      ( k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
% 0.75/0.98      inference(subtyping,[status(esa)],[c_396]) ).
% 0.75/0.98  
% 0.75/0.98  cnf(contradiction,plain,
% 0.75/0.98      ( $false ),
% 0.75/0.98      inference(minisat,[status(thm)],[c_575,c_562,c_15]) ).
% 0.75/0.98  
% 0.75/0.98  
% 0.75/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.75/0.98  
% 0.75/0.98  ------                               Statistics
% 0.75/0.98  
% 0.75/0.98  ------ General
% 0.75/0.98  
% 0.75/0.98  abstr_ref_over_cycles:                  0
% 0.75/0.98  abstr_ref_under_cycles:                 0
% 0.75/0.98  gc_basic_clause_elim:                   0
% 0.75/0.98  forced_gc_time:                         0
% 0.75/0.98  parsing_time:                           0.008
% 0.75/0.98  unif_index_cands_time:                  0.
% 0.75/0.98  unif_index_add_time:                    0.
% 0.75/0.98  orderings_time:                         0.
% 0.75/0.98  out_proof_time:                         0.011
% 0.75/0.98  total_time:                             0.049
% 0.75/0.98  num_of_symbols:                         48
% 0.75/0.98  num_of_terms:                           518
% 0.75/0.98  
% 0.75/0.98  ------ Preprocessing
% 0.75/0.98  
% 0.75/0.98  num_of_splits:                          0
% 0.75/0.98  num_of_split_atoms:                     0
% 0.75/0.98  num_of_reused_defs:                     0
% 0.75/0.98  num_eq_ax_congr_red:                    17
% 0.75/0.98  num_of_sem_filtered_clauses:            0
% 0.75/0.98  num_of_subtypes:                        3
% 0.75/0.98  monotx_restored_types:                  0
% 0.75/0.98  sat_num_of_epr_types:                   0
% 0.75/0.98  sat_num_of_non_cyclic_types:            0
% 0.75/0.98  sat_guarded_non_collapsed_types:        1
% 0.75/0.98  num_pure_diseq_elim:                    0
% 0.75/0.98  simp_replaced_by:                       0
% 0.75/0.98  res_preprocessed:                       26
% 0.75/0.98  prep_upred:                             0
% 0.75/0.98  prep_unflattend:                        17
% 0.75/0.98  smt_new_axioms:                         0
% 0.75/0.98  pred_elim_cands:                        1
% 0.75/0.98  pred_elim:                              10
% 0.75/0.98  pred_elim_cl:                           12
% 0.75/0.98  pred_elim_cycles:                       12
% 0.75/0.98  merged_defs:                            0
% 0.75/0.98  merged_defs_ncl:                        0
% 0.75/0.98  bin_hyper_res:                          0
% 0.75/0.98  prep_cycles:                            2
% 0.75/0.98  pred_elim_time:                         0.005
% 0.75/0.98  splitting_time:                         0.
% 0.75/0.98  sem_filter_time:                        0.
% 0.75/0.98  monotx_time:                            0.
% 0.75/0.98  subtype_inf_time:                       0.
% 0.75/0.98  
% 0.75/0.98  ------ Problem properties
% 0.75/0.98  
% 0.75/0.98  clauses:                                0
% 0.75/0.98  conjectures:                            0
% 0.75/0.98  epr:                                    0
% 0.75/0.98  horn:                                   0
% 0.75/0.98  ground:                                 0
% 0.75/0.98  unary:                                  0
% 0.75/0.98  binary:                                 0
% 0.75/0.98  lits:                                   0
% 0.75/0.98  lits_eq:                                0
% 0.75/0.98  fd_pure:                                0
% 0.75/0.98  fd_pseudo:                              0
% 0.75/0.98  fd_cond:                                0
% 0.75/0.98  fd_pseudo_cond:                         0
% 0.75/0.98  ac_symbols:                             undef
% 0.75/0.98  
% 0.75/0.98  ------ Propositional Solver
% 0.75/0.98  
% 0.75/0.98  prop_solver_calls:                      10
% 0.75/0.98  prop_fast_solver_calls:                 294
% 0.75/0.98  smt_solver_calls:                       0
% 0.75/0.98  smt_fast_solver_calls:                  0
% 0.75/0.98  prop_num_of_clauses:                    164
% 0.75/0.98  prop_preprocess_simplified:             736
% 0.75/0.98  prop_fo_subsumed:                       35
% 0.75/0.98  prop_solver_time:                       0.
% 0.75/0.98  smt_solver_time:                        0.
% 0.75/0.98  smt_fast_solver_time:                   0.
% 0.75/0.98  prop_fast_solver_time:                  0.
% 0.75/0.98  prop_unsat_core_time:                   0.
% 0.75/0.98  
% 0.75/0.98  ------ QBF
% 0.75/0.98  
% 0.75/0.98  qbf_q_res:                              0
% 0.75/0.98  qbf_num_tautologies:                    0
% 0.75/0.98  qbf_prep_cycles:                        0
% 0.75/0.98  
% 0.75/0.98  ------ BMC1
% 0.75/0.98  
% 0.75/0.98  bmc1_current_bound:                     -1
% 0.75/0.98  bmc1_last_solved_bound:                 -1
% 0.75/0.98  bmc1_unsat_core_size:                   -1
% 0.75/0.98  bmc1_unsat_core_parents_size:           -1
% 0.75/0.98  bmc1_merge_next_fun:                    0
% 0.75/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.75/0.98  
% 0.75/0.98  ------ Instantiation
% 0.75/0.98  
% 0.75/0.98  inst_num_of_clauses:                    undef
% 0.75/0.98  inst_num_in_passive:                    undef
% 0.75/0.98  inst_num_in_active:                     0
% 0.75/0.98  inst_num_in_unprocessed:                0
% 0.75/0.98  inst_num_of_loops:                      0
% 0.75/0.98  inst_num_of_learning_restarts:          0
% 0.75/0.98  inst_num_moves_active_passive:          0
% 0.75/0.98  inst_lit_activity:                      0
% 0.75/0.98  inst_lit_activity_moves:                0
% 0.75/0.98  inst_num_tautologies:                   0
% 0.75/0.98  inst_num_prop_implied:                  0
% 0.75/0.98  inst_num_existing_simplified:           0
% 0.75/0.98  inst_num_eq_res_simplified:             0
% 0.75/0.98  inst_num_child_elim:                    0
% 0.75/0.98  inst_num_of_dismatching_blockings:      0
% 0.75/0.98  inst_num_of_non_proper_insts:           0
% 0.75/0.98  inst_num_of_duplicates:                 0
% 0.75/0.98  inst_inst_num_from_inst_to_res:         0
% 0.75/0.98  inst_dismatching_checking_time:         0.
% 0.75/0.98  
% 0.75/0.98  ------ Resolution
% 0.75/0.98  
% 0.75/0.98  res_num_of_clauses:                     7
% 0.75/0.98  res_num_in_passive:                     0
% 0.75/0.98  res_num_in_active:                      0
% 0.75/0.98  res_num_of_loops:                       28
% 0.75/0.98  res_forward_subset_subsumed:            0
% 0.75/0.98  res_backward_subset_subsumed:           0
% 0.75/0.98  res_forward_subsumed:                   0
% 0.75/0.98  res_backward_subsumed:                  0
% 0.75/0.98  res_forward_subsumption_resolution:     0
% 0.75/0.98  res_backward_subsumption_resolution:    0
% 0.75/0.98  res_clause_to_clause_subsumption:       4
% 0.75/0.98  res_orphan_elimination:                 0
% 0.75/0.98  res_tautology_del:                      3
% 0.75/0.98  res_num_eq_res_simplified:              0
% 0.75/0.98  res_num_sel_changes:                    0
% 0.75/0.98  res_moves_from_active_to_pass:          0
% 0.75/0.98  
% 0.75/0.98  ------ Superposition
% 0.75/0.98  
% 0.75/0.98  sup_time_total:                         0.
% 0.75/0.98  sup_time_generating:                    0.
% 0.75/0.98  sup_time_sim_full:                      0.
% 0.75/0.98  sup_time_sim_immed:                     0.
% 0.75/0.98  
% 0.75/0.98  sup_num_of_clauses:                     undef
% 0.75/0.98  sup_num_in_active:                      undef
% 0.75/0.98  sup_num_in_passive:                     undef
% 0.75/0.98  sup_num_of_loops:                       0
% 0.75/0.98  sup_fw_superposition:                   0
% 0.75/0.98  sup_bw_superposition:                   0
% 0.75/0.98  sup_immediate_simplified:               0
% 0.75/0.98  sup_given_eliminated:                   0
% 0.75/0.98  comparisons_done:                       0
% 0.75/0.98  comparisons_avoided:                    0
% 0.75/0.98  
% 0.75/0.98  ------ Simplifications
% 0.75/0.98  
% 0.75/0.98  
% 0.75/0.98  sim_fw_subset_subsumed:                 0
% 0.75/0.98  sim_bw_subset_subsumed:                 0
% 0.75/0.98  sim_fw_subsumed:                        0
% 0.75/0.98  sim_bw_subsumed:                        0
% 0.75/0.98  sim_fw_subsumption_res:                 0
% 0.75/0.98  sim_bw_subsumption_res:                 0
% 0.75/0.98  sim_tautology_del:                      0
% 0.75/0.98  sim_eq_tautology_del:                   0
% 0.75/0.98  sim_eq_res_simp:                        0
% 0.75/0.98  sim_fw_demodulated:                     0
% 0.75/0.98  sim_bw_demodulated:                     0
% 0.75/0.98  sim_light_normalised:                   0
% 0.75/0.98  sim_joinable_taut:                      0
% 0.75/0.98  sim_joinable_simp:                      0
% 0.75/0.98  sim_ac_normalised:                      0
% 0.75/0.98  sim_smt_subsumption:                    0
% 0.75/0.98  
%------------------------------------------------------------------------------

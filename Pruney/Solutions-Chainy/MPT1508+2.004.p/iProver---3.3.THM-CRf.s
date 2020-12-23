%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:13 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 779 expanded)
%              Number of clauses        :   93 ( 184 expanded)
%              Number of leaves         :   16 ( 240 expanded)
%              Depth                    :   25
%              Number of atoms          :  662 (5031 expanded)
%              Number of equality atoms :  114 ( 702 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK4) != X1
        & r3_lattice3(X0,X1,sK4)
        & r2_hidden(X1,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k16_lattice3(X0,X2) != sK3
            & r3_lattice3(X0,sK3,X2)
            & r2_hidden(sK3,X2) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK2,X2) != X1
              & r3_lattice3(sK2,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v4_lattice3(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k16_lattice3(sK2,sK4) != sK3
    & r3_lattice3(sK2,sK3,sK4)
    & r2_hidden(sK3,sK4)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v4_lattice3(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f40,f39,f38])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v4_lattice3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v4_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v4_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v4_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,X3,X4) = k1_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v4_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,X1,sK1(X0)) != k1_lattices(X0,sK1(X0),X1)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,X2,sK0(X0)) != k1_lattices(X0,sK0(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v4_lattices(X0)
          | ( k1_lattices(X0,sK0(X0),sK1(X0)) != k1_lattices(X0,sK1(X0),sK0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,X3,X4) = k1_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v4_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f52,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,X3,X4) = k1_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    r3_lattice3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    k16_lattice3(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_563,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_564,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | k1_lattices(sK2,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_22,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_64,plain,
    ( l2_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r1_lattices(sK2,X0,X1)
    | k1_lattices(sK2,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_22,c_64])).

cnf(c_569,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_lattices(sK2,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_568])).

cnf(c_15,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_307,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_308,plain,
    ( r3_lattices(X0,k16_lattice3(X0,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_23,negated_conjecture,
    ( v4_lattice3(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_345,plain,
    ( r3_lattices(X0,k16_lattice3(X0,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_23])).

cnf(c_346,plain,
    ( r3_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_310,plain,
    ( r3_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v4_lattice3(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_348,plain,
    ( r3_lattices(sK2,k16_lattice3(sK2,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_25,c_24,c_23,c_22,c_21,c_310])).

cnf(c_9,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_404,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_405,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_83,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v9_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_407,plain,
    ( v9_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_25,c_24,c_22,c_83])).

cnf(c_423,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_407])).

cnf(c_424,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v6_lattices(sK2)
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_77,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_80,plain,
    ( v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_428,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_25,c_24,c_22,c_77,c_80])).

cnf(c_429,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_428])).

cnf(c_536,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k16_lattice3(sK2,sK4) != X0
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_429])).

cnf(c_537,plain,
    ( r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
    | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_21])).

cnf(c_540,plain,
    ( r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
    | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_14,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_481,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_482,plain,
    ( m1_subset_1(k16_lattice3(sK2,X0),u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( m1_subset_1(k16_lattice3(sK2,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_25])).

cnf(c_547,plain,
    ( r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_540,c_486])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X1,X0) = X0
    | k16_lattice3(sK2,sK4) != X1
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_569,c_547])).

cnf(c_675,plain,
    ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_677,plain,
    ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_21])).

cnf(c_685,plain,
    ( k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_677,c_486])).

cnf(c_725,plain,
    ( k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
    inference(subtyping,[status(esa)],[c_685])).

cnf(c_729,plain,
    ( m1_subset_1(k16_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_486])).

cnf(c_817,plain,
    ( m1_subset_1(k16_lattice3(sK2,X0_53),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_730,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_816,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X2) = k1_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | k1_lattices(X1,X2,X0) = k1_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | ~ v4_lattices(sK2)
    | k1_lattices(sK2,X0,X1) = k1_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_74,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X0,X1) = k1_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_25,c_24,c_22,c_64,c_74])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X1,X0) = k1_lattices(sK2,X0,X1) ),
    inference(renaming,[status(thm)],[c_616])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | k1_lattices(sK2,X1_51,X0_51) = k1_lattices(sK2,X0_51,X1_51) ),
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_818,plain,
    ( k1_lattices(sK2,X0_51,X1_51) = k1_lattices(sK2,X1_51,X0_51)
    | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_917,plain,
    ( k1_lattices(sK2,X0_51,sK3) = k1_lattices(sK2,sK3,X0_51)
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_818])).

cnf(c_970,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,X0_53)) = k1_lattices(sK2,k16_lattice3(sK2,X0_53),sK3) ),
    inference(superposition,[status(thm)],[c_817,c_917])).

cnf(c_975,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_725,c_970])).

cnf(c_734,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_941,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) != X0_51
    | sK3 != X0_51
    | sK3 = k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_942,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) != sK3
    | sK3 = k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_849,plain,
    ( k16_lattice3(sK2,sK4) != X0_51
    | k16_lattice3(sK2,sK4) = sK3
    | sK3 != X0_51 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_903,plain,
    ( k16_lattice3(sK2,sK4) != k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
    | k16_lattice3(sK2,sK4) = sK3
    | sK3 != k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_861,plain,
    ( X0_51 != X1_51
    | k16_lattice3(sK2,sK4) != X1_51
    | k16_lattice3(sK2,sK4) = X0_51 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_880,plain,
    ( X0_51 != k16_lattice3(sK2,sK4)
    | k16_lattice3(sK2,sK4) = X0_51
    | k16_lattice3(sK2,sK4) != k16_lattice3(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_896,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) != k16_lattice3(sK2,sK4)
    | k16_lattice3(sK2,sK4) = k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
    | k16_lattice3(sK2,sK4) != k16_lattice3(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_733,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_860,plain,
    ( k16_lattice3(sK2,sK4) = k16_lattice3(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_17,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( r3_lattice3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_270,plain,
    ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X1
    | sK4 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_271,plain,
    ( r3_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v4_lattice3(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_273,plain,
    ( r3_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_25,c_24,c_23,c_22,c_21])).

cnf(c_508,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k16_lattice3(sK2,sK4) != X1
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_429])).

cnf(c_509,plain,
    ( r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
    | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_511,plain,
    ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_21])).

cnf(c_512,plain,
    ( r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
    | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_519,plain,
    ( r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_512,c_486])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X1,X0) = X0
    | k16_lattice3(sK2,sK4) != X0
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_569,c_519])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
    | k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_21])).

cnf(c_658,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_650,c_486])).

cnf(c_727,plain,
    ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_658])).

cnf(c_18,negated_conjecture,
    ( k16_lattice3(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_731,negated_conjecture,
    ( k16_lattice3(sK2,sK4) != sK3 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_740,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_975,c_942,c_903,c_896,c_860,c_727,c_731,c_740])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:40:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/0.99  
% 1.18/0.99  ------  iProver source info
% 1.18/0.99  
% 1.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/0.99  git: non_committed_changes: false
% 1.18/0.99  git: last_make_outside_of_git: false
% 1.18/0.99  
% 1.18/0.99  ------ 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options
% 1.18/0.99  
% 1.18/0.99  --out_options                           all
% 1.18/0.99  --tptp_safe_out                         true
% 1.18/0.99  --problem_path                          ""
% 1.18/0.99  --include_path                          ""
% 1.18/0.99  --clausifier                            res/vclausify_rel
% 1.18/0.99  --clausifier_options                    --mode clausify
% 1.18/0.99  --stdin                                 false
% 1.18/0.99  --stats_out                             all
% 1.18/0.99  
% 1.18/0.99  ------ General Options
% 1.18/0.99  
% 1.18/0.99  --fof                                   false
% 1.18/0.99  --time_out_real                         305.
% 1.18/0.99  --time_out_virtual                      -1.
% 1.18/0.99  --symbol_type_check                     false
% 1.18/0.99  --clausify_out                          false
% 1.18/0.99  --sig_cnt_out                           false
% 1.18/0.99  --trig_cnt_out                          false
% 1.18/0.99  --trig_cnt_out_tolerance                1.
% 1.18/0.99  --trig_cnt_out_sk_spl                   false
% 1.18/0.99  --abstr_cl_out                          false
% 1.18/0.99  
% 1.18/0.99  ------ Global Options
% 1.18/0.99  
% 1.18/0.99  --schedule                              default
% 1.18/0.99  --add_important_lit                     false
% 1.18/0.99  --prop_solver_per_cl                    1000
% 1.18/0.99  --min_unsat_core                        false
% 1.18/0.99  --soft_assumptions                      false
% 1.18/0.99  --soft_lemma_size                       3
% 1.18/0.99  --prop_impl_unit_size                   0
% 1.18/0.99  --prop_impl_unit                        []
% 1.18/0.99  --share_sel_clauses                     true
% 1.18/0.99  --reset_solvers                         false
% 1.18/0.99  --bc_imp_inh                            [conj_cone]
% 1.18/0.99  --conj_cone_tolerance                   3.
% 1.18/0.99  --extra_neg_conj                        none
% 1.18/0.99  --large_theory_mode                     true
% 1.18/0.99  --prolific_symb_bound                   200
% 1.18/0.99  --lt_threshold                          2000
% 1.18/0.99  --clause_weak_htbl                      true
% 1.18/0.99  --gc_record_bc_elim                     false
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing Options
% 1.18/0.99  
% 1.18/0.99  --preprocessing_flag                    true
% 1.18/0.99  --time_out_prep_mult                    0.1
% 1.18/0.99  --splitting_mode                        input
% 1.18/0.99  --splitting_grd                         true
% 1.18/0.99  --splitting_cvd                         false
% 1.18/0.99  --splitting_cvd_svl                     false
% 1.18/0.99  --splitting_nvd                         32
% 1.18/0.99  --sub_typing                            true
% 1.18/0.99  --prep_gs_sim                           true
% 1.18/0.99  --prep_unflatten                        true
% 1.18/0.99  --prep_res_sim                          true
% 1.18/0.99  --prep_upred                            true
% 1.18/0.99  --prep_sem_filter                       exhaustive
% 1.18/0.99  --prep_sem_filter_out                   false
% 1.18/0.99  --pred_elim                             true
% 1.18/0.99  --res_sim_input                         true
% 1.18/0.99  --eq_ax_congr_red                       true
% 1.18/0.99  --pure_diseq_elim                       true
% 1.18/0.99  --brand_transform                       false
% 1.18/0.99  --non_eq_to_eq                          false
% 1.18/0.99  --prep_def_merge                        true
% 1.18/0.99  --prep_def_merge_prop_impl              false
% 1.18/0.99  --prep_def_merge_mbd                    true
% 1.18/0.99  --prep_def_merge_tr_red                 false
% 1.18/0.99  --prep_def_merge_tr_cl                  false
% 1.18/0.99  --smt_preprocessing                     true
% 1.18/0.99  --smt_ac_axioms                         fast
% 1.18/0.99  --preprocessed_out                      false
% 1.18/0.99  --preprocessed_stats                    false
% 1.18/0.99  
% 1.18/0.99  ------ Abstraction refinement Options
% 1.18/0.99  
% 1.18/0.99  --abstr_ref                             []
% 1.18/0.99  --abstr_ref_prep                        false
% 1.18/0.99  --abstr_ref_until_sat                   false
% 1.18/0.99  --abstr_ref_sig_restrict                funpre
% 1.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.99  --abstr_ref_under                       []
% 1.18/0.99  
% 1.18/0.99  ------ SAT Options
% 1.18/0.99  
% 1.18/0.99  --sat_mode                              false
% 1.18/0.99  --sat_fm_restart_options                ""
% 1.18/0.99  --sat_gr_def                            false
% 1.18/0.99  --sat_epr_types                         true
% 1.18/0.99  --sat_non_cyclic_types                  false
% 1.18/0.99  --sat_finite_models                     false
% 1.18/0.99  --sat_fm_lemmas                         false
% 1.18/0.99  --sat_fm_prep                           false
% 1.18/0.99  --sat_fm_uc_incr                        true
% 1.18/0.99  --sat_out_model                         small
% 1.18/0.99  --sat_out_clauses                       false
% 1.18/0.99  
% 1.18/0.99  ------ QBF Options
% 1.18/0.99  
% 1.18/0.99  --qbf_mode                              false
% 1.18/0.99  --qbf_elim_univ                         false
% 1.18/0.99  --qbf_dom_inst                          none
% 1.18/0.99  --qbf_dom_pre_inst                      false
% 1.18/0.99  --qbf_sk_in                             false
% 1.18/0.99  --qbf_pred_elim                         true
% 1.18/0.99  --qbf_split                             512
% 1.18/0.99  
% 1.18/0.99  ------ BMC1 Options
% 1.18/0.99  
% 1.18/0.99  --bmc1_incremental                      false
% 1.18/0.99  --bmc1_axioms                           reachable_all
% 1.18/0.99  --bmc1_min_bound                        0
% 1.18/0.99  --bmc1_max_bound                        -1
% 1.18/0.99  --bmc1_max_bound_default                -1
% 1.18/0.99  --bmc1_symbol_reachability              true
% 1.18/0.99  --bmc1_property_lemmas                  false
% 1.18/0.99  --bmc1_k_induction                      false
% 1.18/0.99  --bmc1_non_equiv_states                 false
% 1.18/0.99  --bmc1_deadlock                         false
% 1.18/0.99  --bmc1_ucm                              false
% 1.18/0.99  --bmc1_add_unsat_core                   none
% 1.18/0.99  --bmc1_unsat_core_children              false
% 1.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.99  --bmc1_out_stat                         full
% 1.18/0.99  --bmc1_ground_init                      false
% 1.18/0.99  --bmc1_pre_inst_next_state              false
% 1.18/0.99  --bmc1_pre_inst_state                   false
% 1.18/0.99  --bmc1_pre_inst_reach_state             false
% 1.18/0.99  --bmc1_out_unsat_core                   false
% 1.18/0.99  --bmc1_aig_witness_out                  false
% 1.18/0.99  --bmc1_verbose                          false
% 1.18/0.99  --bmc1_dump_clauses_tptp                false
% 1.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.99  --bmc1_dump_file                        -
% 1.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.99  --bmc1_ucm_extend_mode                  1
% 1.18/0.99  --bmc1_ucm_init_mode                    2
% 1.18/0.99  --bmc1_ucm_cone_mode                    none
% 1.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.99  --bmc1_ucm_relax_model                  4
% 1.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.99  --bmc1_ucm_layered_model                none
% 1.18/0.99  --bmc1_ucm_max_lemma_size               10
% 1.18/0.99  
% 1.18/0.99  ------ AIG Options
% 1.18/0.99  
% 1.18/0.99  --aig_mode                              false
% 1.18/0.99  
% 1.18/0.99  ------ Instantiation Options
% 1.18/0.99  
% 1.18/0.99  --instantiation_flag                    true
% 1.18/0.99  --inst_sos_flag                         false
% 1.18/0.99  --inst_sos_phase                        true
% 1.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel_side                     num_symb
% 1.18/0.99  --inst_solver_per_active                1400
% 1.18/0.99  --inst_solver_calls_frac                1.
% 1.18/0.99  --inst_passive_queue_type               priority_queues
% 1.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.99  --inst_passive_queues_freq              [25;2]
% 1.18/0.99  --inst_dismatching                      true
% 1.18/0.99  --inst_eager_unprocessed_to_passive     true
% 1.18/0.99  --inst_prop_sim_given                   true
% 1.18/0.99  --inst_prop_sim_new                     false
% 1.18/0.99  --inst_subs_new                         false
% 1.18/0.99  --inst_eq_res_simp                      false
% 1.18/0.99  --inst_subs_given                       false
% 1.18/0.99  --inst_orphan_elimination               true
% 1.18/0.99  --inst_learning_loop_flag               true
% 1.18/0.99  --inst_learning_start                   3000
% 1.18/0.99  --inst_learning_factor                  2
% 1.18/0.99  --inst_start_prop_sim_after_learn       3
% 1.18/0.99  --inst_sel_renew                        solver
% 1.18/0.99  --inst_lit_activity_flag                true
% 1.18/0.99  --inst_restr_to_given                   false
% 1.18/0.99  --inst_activity_threshold               500
% 1.18/0.99  --inst_out_proof                        true
% 1.18/0.99  
% 1.18/0.99  ------ Resolution Options
% 1.18/0.99  
% 1.18/0.99  --resolution_flag                       true
% 1.18/0.99  --res_lit_sel                           adaptive
% 1.18/0.99  --res_lit_sel_side                      none
% 1.18/0.99  --res_ordering                          kbo
% 1.18/0.99  --res_to_prop_solver                    active
% 1.18/0.99  --res_prop_simpl_new                    false
% 1.18/0.99  --res_prop_simpl_given                  true
% 1.18/0.99  --res_passive_queue_type                priority_queues
% 1.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.99  --res_passive_queues_freq               [15;5]
% 1.18/0.99  --res_forward_subs                      full
% 1.18/0.99  --res_backward_subs                     full
% 1.18/0.99  --res_forward_subs_resolution           true
% 1.18/0.99  --res_backward_subs_resolution          true
% 1.18/0.99  --res_orphan_elimination                true
% 1.18/0.99  --res_time_limit                        2.
% 1.18/0.99  --res_out_proof                         true
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Options
% 1.18/0.99  
% 1.18/0.99  --superposition_flag                    true
% 1.18/0.99  --sup_passive_queue_type                priority_queues
% 1.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.99  --demod_completeness_check              fast
% 1.18/0.99  --demod_use_ground                      true
% 1.18/0.99  --sup_to_prop_solver                    passive
% 1.18/0.99  --sup_prop_simpl_new                    true
% 1.18/0.99  --sup_prop_simpl_given                  true
% 1.18/0.99  --sup_fun_splitting                     false
% 1.18/0.99  --sup_smt_interval                      50000
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Simplification Setup
% 1.18/0.99  
% 1.18/0.99  --sup_indices_passive                   []
% 1.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_full_bw                           [BwDemod]
% 1.18/0.99  --sup_immed_triv                        [TrivRules]
% 1.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_immed_bw_main                     []
% 1.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  
% 1.18/0.99  ------ Combination Options
% 1.18/0.99  
% 1.18/0.99  --comb_res_mult                         3
% 1.18/0.99  --comb_sup_mult                         2
% 1.18/0.99  --comb_inst_mult                        10
% 1.18/0.99  
% 1.18/0.99  ------ Debug Options
% 1.18/0.99  
% 1.18/0.99  --dbg_backtrace                         false
% 1.18/0.99  --dbg_dump_prop_clauses                 false
% 1.18/0.99  --dbg_dump_prop_clauses_file            -
% 1.18/0.99  --dbg_out_stat                          false
% 1.18/0.99  ------ Parsing...
% 1.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.18/0.99  ------ Proving...
% 1.18/0.99  ------ Problem Properties 
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  clauses                                 7
% 1.18/0.99  conjectures                             2
% 1.18/0.99  EPR                                     0
% 1.18/0.99  Horn                                    7
% 1.18/0.99  unary                                   5
% 1.18/0.99  binary                                  1
% 1.18/0.99  lits                                    10
% 1.18/0.99  lits eq                                 5
% 1.18/0.99  fd_pure                                 0
% 1.18/0.99  fd_pseudo                               0
% 1.18/0.99  fd_cond                                 0
% 1.18/0.99  fd_pseudo_cond                          0
% 1.18/0.99  AC symbols                              0
% 1.18/0.99  
% 1.18/0.99  ------ Schedule dynamic 5 is on 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  ------ 
% 1.18/0.99  Current options:
% 1.18/0.99  ------ 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options
% 1.18/0.99  
% 1.18/0.99  --out_options                           all
% 1.18/0.99  --tptp_safe_out                         true
% 1.18/0.99  --problem_path                          ""
% 1.18/0.99  --include_path                          ""
% 1.18/0.99  --clausifier                            res/vclausify_rel
% 1.18/0.99  --clausifier_options                    --mode clausify
% 1.18/0.99  --stdin                                 false
% 1.18/0.99  --stats_out                             all
% 1.18/0.99  
% 1.18/0.99  ------ General Options
% 1.18/0.99  
% 1.18/0.99  --fof                                   false
% 1.18/0.99  --time_out_real                         305.
% 1.18/0.99  --time_out_virtual                      -1.
% 1.18/0.99  --symbol_type_check                     false
% 1.18/0.99  --clausify_out                          false
% 1.18/0.99  --sig_cnt_out                           false
% 1.18/0.99  --trig_cnt_out                          false
% 1.18/0.99  --trig_cnt_out_tolerance                1.
% 1.18/0.99  --trig_cnt_out_sk_spl                   false
% 1.18/0.99  --abstr_cl_out                          false
% 1.18/0.99  
% 1.18/0.99  ------ Global Options
% 1.18/0.99  
% 1.18/0.99  --schedule                              default
% 1.18/0.99  --add_important_lit                     false
% 1.18/0.99  --prop_solver_per_cl                    1000
% 1.18/0.99  --min_unsat_core                        false
% 1.18/0.99  --soft_assumptions                      false
% 1.18/0.99  --soft_lemma_size                       3
% 1.18/0.99  --prop_impl_unit_size                   0
% 1.18/0.99  --prop_impl_unit                        []
% 1.18/0.99  --share_sel_clauses                     true
% 1.18/0.99  --reset_solvers                         false
% 1.18/0.99  --bc_imp_inh                            [conj_cone]
% 1.18/0.99  --conj_cone_tolerance                   3.
% 1.18/0.99  --extra_neg_conj                        none
% 1.18/0.99  --large_theory_mode                     true
% 1.18/0.99  --prolific_symb_bound                   200
% 1.18/0.99  --lt_threshold                          2000
% 1.18/0.99  --clause_weak_htbl                      true
% 1.18/0.99  --gc_record_bc_elim                     false
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing Options
% 1.18/0.99  
% 1.18/0.99  --preprocessing_flag                    true
% 1.18/0.99  --time_out_prep_mult                    0.1
% 1.18/0.99  --splitting_mode                        input
% 1.18/0.99  --splitting_grd                         true
% 1.18/0.99  --splitting_cvd                         false
% 1.18/0.99  --splitting_cvd_svl                     false
% 1.18/0.99  --splitting_nvd                         32
% 1.18/0.99  --sub_typing                            true
% 1.18/0.99  --prep_gs_sim                           true
% 1.18/0.99  --prep_unflatten                        true
% 1.18/0.99  --prep_res_sim                          true
% 1.18/0.99  --prep_upred                            true
% 1.18/0.99  --prep_sem_filter                       exhaustive
% 1.18/0.99  --prep_sem_filter_out                   false
% 1.18/0.99  --pred_elim                             true
% 1.18/0.99  --res_sim_input                         true
% 1.18/0.99  --eq_ax_congr_red                       true
% 1.18/0.99  --pure_diseq_elim                       true
% 1.18/0.99  --brand_transform                       false
% 1.18/0.99  --non_eq_to_eq                          false
% 1.18/0.99  --prep_def_merge                        true
% 1.18/0.99  --prep_def_merge_prop_impl              false
% 1.18/0.99  --prep_def_merge_mbd                    true
% 1.18/0.99  --prep_def_merge_tr_red                 false
% 1.18/0.99  --prep_def_merge_tr_cl                  false
% 1.18/0.99  --smt_preprocessing                     true
% 1.18/0.99  --smt_ac_axioms                         fast
% 1.18/0.99  --preprocessed_out                      false
% 1.18/0.99  --preprocessed_stats                    false
% 1.18/0.99  
% 1.18/0.99  ------ Abstraction refinement Options
% 1.18/0.99  
% 1.18/0.99  --abstr_ref                             []
% 1.18/0.99  --abstr_ref_prep                        false
% 1.18/0.99  --abstr_ref_until_sat                   false
% 1.18/0.99  --abstr_ref_sig_restrict                funpre
% 1.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.99  --abstr_ref_under                       []
% 1.18/0.99  
% 1.18/0.99  ------ SAT Options
% 1.18/0.99  
% 1.18/0.99  --sat_mode                              false
% 1.18/0.99  --sat_fm_restart_options                ""
% 1.18/0.99  --sat_gr_def                            false
% 1.18/0.99  --sat_epr_types                         true
% 1.18/0.99  --sat_non_cyclic_types                  false
% 1.18/0.99  --sat_finite_models                     false
% 1.18/0.99  --sat_fm_lemmas                         false
% 1.18/0.99  --sat_fm_prep                           false
% 1.18/0.99  --sat_fm_uc_incr                        true
% 1.18/0.99  --sat_out_model                         small
% 1.18/0.99  --sat_out_clauses                       false
% 1.18/0.99  
% 1.18/0.99  ------ QBF Options
% 1.18/0.99  
% 1.18/0.99  --qbf_mode                              false
% 1.18/0.99  --qbf_elim_univ                         false
% 1.18/0.99  --qbf_dom_inst                          none
% 1.18/0.99  --qbf_dom_pre_inst                      false
% 1.18/0.99  --qbf_sk_in                             false
% 1.18/0.99  --qbf_pred_elim                         true
% 1.18/0.99  --qbf_split                             512
% 1.18/0.99  
% 1.18/0.99  ------ BMC1 Options
% 1.18/0.99  
% 1.18/0.99  --bmc1_incremental                      false
% 1.18/0.99  --bmc1_axioms                           reachable_all
% 1.18/0.99  --bmc1_min_bound                        0
% 1.18/0.99  --bmc1_max_bound                        -1
% 1.18/0.99  --bmc1_max_bound_default                -1
% 1.18/0.99  --bmc1_symbol_reachability              true
% 1.18/0.99  --bmc1_property_lemmas                  false
% 1.18/0.99  --bmc1_k_induction                      false
% 1.18/0.99  --bmc1_non_equiv_states                 false
% 1.18/0.99  --bmc1_deadlock                         false
% 1.18/0.99  --bmc1_ucm                              false
% 1.18/0.99  --bmc1_add_unsat_core                   none
% 1.18/0.99  --bmc1_unsat_core_children              false
% 1.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.99  --bmc1_out_stat                         full
% 1.18/0.99  --bmc1_ground_init                      false
% 1.18/0.99  --bmc1_pre_inst_next_state              false
% 1.18/0.99  --bmc1_pre_inst_state                   false
% 1.18/0.99  --bmc1_pre_inst_reach_state             false
% 1.18/0.99  --bmc1_out_unsat_core                   false
% 1.18/0.99  --bmc1_aig_witness_out                  false
% 1.18/0.99  --bmc1_verbose                          false
% 1.18/0.99  --bmc1_dump_clauses_tptp                false
% 1.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.99  --bmc1_dump_file                        -
% 1.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.99  --bmc1_ucm_extend_mode                  1
% 1.18/0.99  --bmc1_ucm_init_mode                    2
% 1.18/0.99  --bmc1_ucm_cone_mode                    none
% 1.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.99  --bmc1_ucm_relax_model                  4
% 1.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.99  --bmc1_ucm_layered_model                none
% 1.18/0.99  --bmc1_ucm_max_lemma_size               10
% 1.18/0.99  
% 1.18/0.99  ------ AIG Options
% 1.18/0.99  
% 1.18/0.99  --aig_mode                              false
% 1.18/0.99  
% 1.18/0.99  ------ Instantiation Options
% 1.18/0.99  
% 1.18/0.99  --instantiation_flag                    true
% 1.18/0.99  --inst_sos_flag                         false
% 1.18/0.99  --inst_sos_phase                        true
% 1.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel_side                     none
% 1.18/0.99  --inst_solver_per_active                1400
% 1.18/0.99  --inst_solver_calls_frac                1.
% 1.18/0.99  --inst_passive_queue_type               priority_queues
% 1.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.99  --inst_passive_queues_freq              [25;2]
% 1.18/0.99  --inst_dismatching                      true
% 1.18/0.99  --inst_eager_unprocessed_to_passive     true
% 1.18/0.99  --inst_prop_sim_given                   true
% 1.18/0.99  --inst_prop_sim_new                     false
% 1.18/0.99  --inst_subs_new                         false
% 1.18/0.99  --inst_eq_res_simp                      false
% 1.18/0.99  --inst_subs_given                       false
% 1.18/0.99  --inst_orphan_elimination               true
% 1.18/0.99  --inst_learning_loop_flag               true
% 1.18/0.99  --inst_learning_start                   3000
% 1.18/0.99  --inst_learning_factor                  2
% 1.18/0.99  --inst_start_prop_sim_after_learn       3
% 1.18/0.99  --inst_sel_renew                        solver
% 1.18/0.99  --inst_lit_activity_flag                true
% 1.18/0.99  --inst_restr_to_given                   false
% 1.18/0.99  --inst_activity_threshold               500
% 1.18/0.99  --inst_out_proof                        true
% 1.18/0.99  
% 1.18/0.99  ------ Resolution Options
% 1.18/0.99  
% 1.18/0.99  --resolution_flag                       false
% 1.18/0.99  --res_lit_sel                           adaptive
% 1.18/0.99  --res_lit_sel_side                      none
% 1.18/0.99  --res_ordering                          kbo
% 1.18/0.99  --res_to_prop_solver                    active
% 1.18/0.99  --res_prop_simpl_new                    false
% 1.18/0.99  --res_prop_simpl_given                  true
% 1.18/0.99  --res_passive_queue_type                priority_queues
% 1.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.99  --res_passive_queues_freq               [15;5]
% 1.18/0.99  --res_forward_subs                      full
% 1.18/0.99  --res_backward_subs                     full
% 1.18/0.99  --res_forward_subs_resolution           true
% 1.18/0.99  --res_backward_subs_resolution          true
% 1.18/0.99  --res_orphan_elimination                true
% 1.18/0.99  --res_time_limit                        2.
% 1.18/0.99  --res_out_proof                         true
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Options
% 1.18/0.99  
% 1.18/0.99  --superposition_flag                    true
% 1.18/0.99  --sup_passive_queue_type                priority_queues
% 1.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.99  --demod_completeness_check              fast
% 1.18/0.99  --demod_use_ground                      true
% 1.18/0.99  --sup_to_prop_solver                    passive
% 1.18/0.99  --sup_prop_simpl_new                    true
% 1.18/0.99  --sup_prop_simpl_given                  true
% 1.18/0.99  --sup_fun_splitting                     false
% 1.18/0.99  --sup_smt_interval                      50000
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Simplification Setup
% 1.18/0.99  
% 1.18/0.99  --sup_indices_passive                   []
% 1.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_full_bw                           [BwDemod]
% 1.18/0.99  --sup_immed_triv                        [TrivRules]
% 1.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_immed_bw_main                     []
% 1.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  
% 1.18/0.99  ------ Combination Options
% 1.18/0.99  
% 1.18/0.99  --comb_res_mult                         3
% 1.18/0.99  --comb_sup_mult                         2
% 1.18/0.99  --comb_inst_mult                        10
% 1.18/0.99  
% 1.18/0.99  ------ Debug Options
% 1.18/0.99  
% 1.18/0.99  --dbg_backtrace                         false
% 1.18/0.99  --dbg_dump_prop_clauses                 false
% 1.18/0.99  --dbg_dump_prop_clauses_file            -
% 1.18/0.99  --dbg_out_stat                          false
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  ------ Proving...
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  % SZS status Theorem for theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  fof(f2,axiom,(
% 1.18/0.99    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f16,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f2])).
% 1.18/0.99  
% 1.18/0.99  fof(f17,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f16])).
% 1.18/0.99  
% 1.18/0.99  fof(f31,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(nnf_transformation,[],[f17])).
% 1.18/0.99  
% 1.18/0.99  fof(f47,plain,(
% 1.18/0.99    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f31])).
% 1.18/0.99  
% 1.18/0.99  fof(f9,conjecture,(
% 1.18/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f10,negated_conjecture,(
% 1.18/0.99    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.18/0.99    inference(negated_conjecture,[],[f9])).
% 1.18/0.99  
% 1.18/0.99  fof(f29,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f10])).
% 1.18/0.99  
% 1.18/0.99  fof(f30,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f29])).
% 1.18/0.99  
% 1.18/0.99  fof(f40,plain,(
% 1.18/0.99    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK4) != X1 & r3_lattice3(X0,X1,sK4) & r2_hidden(X1,sK4))) )),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f39,plain,(
% 1.18/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK3 & r3_lattice3(X0,sK3,X2) & r2_hidden(sK3,X2)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f38,plain,(
% 1.18/0.99    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK2,X2) != X1 & r3_lattice3(sK2,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v4_lattice3(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f41,plain,(
% 1.18/0.99    ((k16_lattice3(sK2,sK4) != sK3 & r3_lattice3(sK2,sK3,sK4) & r2_hidden(sK3,sK4)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v4_lattice3(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 1.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f40,f39,f38])).
% 1.18/0.99  
% 1.18/0.99  fof(f60,plain,(
% 1.18/0.99    ~v2_struct_0(sK2)),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f63,plain,(
% 1.18/0.99    l3_lattices(sK2)),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f3,axiom,(
% 1.18/0.99    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f11,plain,(
% 1.18/0.99    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.18/0.99    inference(pure_predicate_removal,[],[f3])).
% 1.18/0.99  
% 1.18/0.99  fof(f18,plain,(
% 1.18/0.99    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.18/0.99    inference(ennf_transformation,[],[f11])).
% 1.18/0.99  
% 1.18/0.99  fof(f49,plain,(
% 1.18/0.99    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f18])).
% 1.18/0.99  
% 1.18/0.99  fof(f7,axiom,(
% 1.18/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f25,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f7])).
% 1.18/0.99  
% 1.18/0.99  fof(f26,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f25])).
% 1.18/0.99  
% 1.18/0.99  fof(f58,plain,(
% 1.18/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f26])).
% 1.18/0.99  
% 1.18/0.99  fof(f65,plain,(
% 1.18/0.99    r2_hidden(sK3,sK4)),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f62,plain,(
% 1.18/0.99    v4_lattice3(sK2)),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f61,plain,(
% 1.18/0.99    v10_lattices(sK2)),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f64,plain,(
% 1.18/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f4,axiom,(
% 1.18/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f19,plain,(
% 1.18/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f4])).
% 1.18/0.99  
% 1.18/0.99  fof(f20,plain,(
% 1.18/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f19])).
% 1.18/0.99  
% 1.18/0.99  fof(f32,plain,(
% 1.18/0.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(nnf_transformation,[],[f20])).
% 1.18/0.99  
% 1.18/0.99  fof(f50,plain,(
% 1.18/0.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f32])).
% 1.18/0.99  
% 1.18/0.99  fof(f1,axiom,(
% 1.18/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f12,plain,(
% 1.18/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.18/0.99    inference(pure_predicate_removal,[],[f1])).
% 1.18/0.99  
% 1.18/0.99  fof(f13,plain,(
% 1.18/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.18/0.99    inference(pure_predicate_removal,[],[f12])).
% 1.18/0.99  
% 1.18/0.99  fof(f14,plain,(
% 1.18/0.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.18/0.99    inference(ennf_transformation,[],[f13])).
% 1.18/0.99  
% 1.18/0.99  fof(f15,plain,(
% 1.18/0.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.18/0.99    inference(flattening,[],[f14])).
% 1.18/0.99  
% 1.18/0.99  fof(f46,plain,(
% 1.18/0.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f15])).
% 1.18/0.99  
% 1.18/0.99  fof(f44,plain,(
% 1.18/0.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f15])).
% 1.18/0.99  
% 1.18/0.99  fof(f45,plain,(
% 1.18/0.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f15])).
% 1.18/0.99  
% 1.18/0.99  fof(f6,axiom,(
% 1.18/0.99    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f23,plain,(
% 1.18/0.99    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f6])).
% 1.18/0.99  
% 1.18/0.99  fof(f24,plain,(
% 1.18/0.99    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f23])).
% 1.18/0.99  
% 1.18/0.99  fof(f56,plain,(
% 1.18/0.99    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f24])).
% 1.18/0.99  
% 1.18/0.99  fof(f5,axiom,(
% 1.18/0.99    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f21,plain,(
% 1.18/0.99    ! [X0] : ((v4_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f5])).
% 1.18/0.99  
% 1.18/0.99  fof(f22,plain,(
% 1.18/0.99    ! [X0] : ((v4_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f21])).
% 1.18/0.99  
% 1.18/0.99  fof(f33,plain,(
% 1.18/0.99    ! [X0] : (((v4_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v4_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(nnf_transformation,[],[f22])).
% 1.18/0.99  
% 1.18/0.99  fof(f34,plain,(
% 1.18/0.99    ! [X0] : (((v4_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,X3,X4) = k1_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v4_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(rectify,[],[f33])).
% 1.18/0.99  
% 1.18/0.99  fof(f36,plain,(
% 1.18/0.99    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,X1,sK1(X0)) != k1_lattices(X0,sK1(X0),X1) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f35,plain,(
% 1.18/0.99    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,X1,X2) != k1_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,X2,sK0(X0)) != k1_lattices(X0,sK0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 1.18/0.99    introduced(choice_axiom,[])).
% 1.18/0.99  
% 1.18/0.99  fof(f37,plain,(
% 1.18/0.99    ! [X0] : (((v4_lattices(X0) | ((k1_lattices(X0,sK0(X0),sK1(X0)) != k1_lattices(X0,sK1(X0),sK0(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,X3,X4) = k1_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v4_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 1.18/0.99  
% 1.18/0.99  fof(f52,plain,(
% 1.18/0.99    ( ! [X4,X0,X3] : (k1_lattices(X0,X3,X4) = k1_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f37])).
% 1.18/0.99  
% 1.18/0.99  fof(f43,plain,(
% 1.18/0.99    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f15])).
% 1.18/0.99  
% 1.18/0.99  fof(f8,axiom,(
% 1.18/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 1.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.99  
% 1.18/0.99  fof(f27,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.99    inference(ennf_transformation,[],[f8])).
% 1.18/0.99  
% 1.18/0.99  fof(f28,plain,(
% 1.18/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.99    inference(flattening,[],[f27])).
% 1.18/0.99  
% 1.18/0.99  fof(f59,plain,(
% 1.18/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.99    inference(cnf_transformation,[],[f28])).
% 1.18/0.99  
% 1.18/0.99  fof(f66,plain,(
% 1.18/0.99    r3_lattice3(sK2,sK3,sK4)),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  fof(f67,plain,(
% 1.18/0.99    k16_lattice3(sK2,sK4) != sK3),
% 1.18/0.99    inference(cnf_transformation,[],[f41])).
% 1.18/0.99  
% 1.18/0.99  cnf(c_6,plain,
% 1.18/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.99      | ~ l2_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | k1_lattices(X0,X1,X2) = X2 ),
% 1.18/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_25,negated_conjecture,
% 1.18/0.99      ( ~ v2_struct_0(sK2) ),
% 1.18/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_563,plain,
% 1.18/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.99      | ~ l2_lattices(X0)
% 1.18/0.99      | k1_lattices(X0,X1,X2) = X2
% 1.18/0.99      | sK2 != X0 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_564,plain,
% 1.18/0.99      ( ~ r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ l2_lattices(sK2)
% 1.18/0.99      | k1_lattices(sK2,X0,X1) = X1 ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_563]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_22,negated_conjecture,
% 1.18/0.99      ( l3_lattices(sK2) ),
% 1.18/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_7,plain,
% 1.18/0.99      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_64,plain,
% 1.18/0.99      ( l2_lattices(sK2) | ~ l3_lattices(sK2) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_568,plain,
% 1.18/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ r1_lattices(sK2,X0,X1)
% 1.18/0.99      | k1_lattices(sK2,X0,X1) = X1 ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_564,c_22,c_64]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_569,plain,
% 1.18/0.99      ( ~ r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,X0,X1) = X1 ),
% 1.18/0.99      inference(renaming,[status(thm)],[c_568]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_15,plain,
% 1.18/0.99      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 1.18/0.99      | ~ r2_hidden(X2,X1)
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.99      | ~ v4_lattice3(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_20,negated_conjecture,
% 1.18/0.99      ( r2_hidden(sK3,sK4) ),
% 1.18/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_307,plain,
% 1.18/0.99      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.99      | ~ v4_lattice3(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0)
% 1.18/0.99      | sK3 != X2
% 1.18/0.99      | sK4 != X1 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_308,plain,
% 1.18/0.99      ( r3_lattices(X0,k16_lattice3(X0,sK4),sK3)
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(X0))
% 1.18/0.99      | ~ v4_lattice3(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_307]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_23,negated_conjecture,
% 1.18/0.99      ( v4_lattice3(sK2) ),
% 1.18/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_345,plain,
% 1.18/0.99      ( r3_lattices(X0,k16_lattice3(X0,sK4),sK3)
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(X0))
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0)
% 1.18/0.99      | sK2 != X0 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_308,c_23]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_346,plain,
% 1.18/0.99      ( r3_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_24,negated_conjecture,
% 1.18/0.99      ( v10_lattices(sK2) ),
% 1.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_21,negated_conjecture,
% 1.18/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.18/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_310,plain,
% 1.18/0.99      ( r3_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.18/0.99      | ~ v4_lattice3(sK2)
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_308]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_348,plain,
% 1.18/0.99      ( r3_lattices(sK2,k16_lattice3(sK2,sK4),sK3) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_346,c_25,c_24,c_23,c_22,c_21,c_310]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_9,plain,
% 1.18/0.99      ( ~ r3_lattices(X0,X1,X2)
% 1.18/0.99      | r1_lattices(X0,X1,X2)
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.99      | ~ v6_lattices(X0)
% 1.18/0.99      | ~ v8_lattices(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v9_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_0,plain,
% 1.18/0.99      ( ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0)
% 1.18/0.99      | v9_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_404,plain,
% 1.18/0.99      ( ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | v9_lattices(X0)
% 1.18/0.99      | sK2 != X0 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_405,plain,
% 1.18/0.99      ( ~ l3_lattices(sK2) | v2_struct_0(sK2) | v9_lattices(sK2) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_404]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_83,plain,
% 1.18/0.99      ( ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2)
% 1.18/0.99      | v9_lattices(sK2) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_407,plain,
% 1.18/0.99      ( v9_lattices(sK2) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_405,c_25,c_24,c_22,c_83]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_423,plain,
% 1.18/0.99      ( ~ r3_lattices(X0,X1,X2)
% 1.18/0.99      | r1_lattices(X0,X1,X2)
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.99      | ~ v6_lattices(X0)
% 1.18/0.99      | ~ v8_lattices(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | sK2 != X0 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_407]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_424,plain,
% 1.18/0.99      ( ~ r3_lattices(sK2,X0,X1)
% 1.18/0.99      | r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ v6_lattices(sK2)
% 1.18/0.99      | ~ v8_lattices(sK2)
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_423]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_2,plain,
% 1.18/0.99      ( v6_lattices(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_77,plain,
% 1.18/0.99      ( v6_lattices(sK2)
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_1,plain,
% 1.18/0.99      ( v8_lattices(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_80,plain,
% 1.18/0.99      ( v8_lattices(sK2)
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_428,plain,
% 1.18/0.99      ( ~ r3_lattices(sK2,X0,X1)
% 1.18/0.99      | r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_424,c_25,c_24,c_22,c_77,c_80]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_429,plain,
% 1.18/0.99      ( ~ r3_lattices(sK2,X0,X1)
% 1.18/0.99      | r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.18/0.99      inference(renaming,[status(thm)],[c_428]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_536,plain,
% 1.18/0.99      ( r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | k16_lattice3(sK2,sK4) != X0
% 1.18/0.99      | sK3 != X1
% 1.18/0.99      | sK2 != sK2 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_348,c_429]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_537,plain,
% 1.18/0.99      ( r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
% 1.18/0.99      | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_539,plain,
% 1.18/0.99      ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_537,c_21]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_540,plain,
% 1.18/0.99      ( r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3)
% 1.18/0.99      | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
% 1.18/0.99      inference(renaming,[status(thm)],[c_539]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_14,plain,
% 1.18/0.99      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_481,plain,
% 1.18/0.99      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | sK2 != X0 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_482,plain,
% 1.18/0.99      ( m1_subset_1(k16_lattice3(sK2,X0),u1_struct_0(sK2))
% 1.18/0.99      | v2_struct_0(sK2) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_486,plain,
% 1.18/0.99      ( m1_subset_1(k16_lattice3(sK2,X0),u1_struct_0(sK2)) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_482,c_25]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_547,plain,
% 1.18/0.99      ( r1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) ),
% 1.18/0.99      inference(forward_subsumption_resolution,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_540,c_486]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_674,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,X1,X0) = X0
% 1.18/0.99      | k16_lattice3(sK2,sK4) != X1
% 1.18/0.99      | sK3 != X0
% 1.18/0.99      | sK2 != sK2 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_569,c_547]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_675,plain,
% 1.18/0.99      ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_674]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_677,plain,
% 1.18/0.99      ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_675,c_21]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_685,plain,
% 1.18/0.99      ( k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
% 1.18/0.99      inference(forward_subsumption_resolution,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_677,c_486]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_725,plain,
% 1.18/0.99      ( k1_lattices(sK2,k16_lattice3(sK2,sK4),sK3) = sK3 ),
% 1.18/0.99      inference(subtyping,[status(esa)],[c_685]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_729,plain,
% 1.18/0.99      ( m1_subset_1(k16_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
% 1.18/0.99      inference(subtyping,[status(esa)],[c_486]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_817,plain,
% 1.18/0.99      ( m1_subset_1(k16_lattice3(sK2,X0_53),u1_struct_0(sK2)) = iProver_top ),
% 1.18/0.99      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_730,negated_conjecture,
% 1.18/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.18/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_816,plain,
% 1.18/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.18/0.99      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_13,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.18/0.99      | ~ l2_lattices(X1)
% 1.18/0.99      | ~ v4_lattices(X1)
% 1.18/0.99      | v2_struct_0(X1)
% 1.18/0.99      | k1_lattices(X1,X0,X2) = k1_lattices(X1,X2,X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_611,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.18/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.18/0.99      | ~ l2_lattices(X1)
% 1.18/0.99      | ~ v4_lattices(X1)
% 1.18/0.99      | k1_lattices(X1,X2,X0) = k1_lattices(X1,X0,X2)
% 1.18/0.99      | sK2 != X1 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_612,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ l2_lattices(sK2)
% 1.18/0.99      | ~ v4_lattices(sK2)
% 1.18/0.99      | k1_lattices(sK2,X0,X1) = k1_lattices(sK2,X1,X0) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_611]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_3,plain,
% 1.18/0.99      ( v4_lattices(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_74,plain,
% 1.18/0.99      ( v4_lattices(sK2)
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_616,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,X0,X1) = k1_lattices(sK2,X1,X0) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_612,c_25,c_24,c_22,c_64,c_74]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_617,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,X1,X0) = k1_lattices(sK2,X0,X1) ),
% 1.18/0.99      inference(renaming,[status(thm)],[c_616]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_728,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,X1_51,X0_51) = k1_lattices(sK2,X0_51,X1_51) ),
% 1.18/0.99      inference(subtyping,[status(esa)],[c_617]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_818,plain,
% 1.18/0.99      ( k1_lattices(sK2,X0_51,X1_51) = k1_lattices(sK2,X1_51,X0_51)
% 1.18/0.99      | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
% 1.18/0.99      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 1.18/0.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_917,plain,
% 1.18/0.99      ( k1_lattices(sK2,X0_51,sK3) = k1_lattices(sK2,sK3,X0_51)
% 1.18/0.99      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 1.18/0.99      inference(superposition,[status(thm)],[c_816,c_818]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_970,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,X0_53)) = k1_lattices(sK2,k16_lattice3(sK2,X0_53),sK3) ),
% 1.18/0.99      inference(superposition,[status(thm)],[c_817,c_917]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_975,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = sK3 ),
% 1.18/0.99      inference(superposition,[status(thm)],[c_725,c_970]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_734,plain,
% 1.18/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 1.18/0.99      theory(equality) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_941,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) != X0_51
% 1.18/0.99      | sK3 != X0_51
% 1.18/0.99      | sK3 = k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_734]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_942,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) != sK3
% 1.18/0.99      | sK3 = k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
% 1.18/0.99      | sK3 != sK3 ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_941]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_849,plain,
% 1.18/0.99      ( k16_lattice3(sK2,sK4) != X0_51
% 1.18/0.99      | k16_lattice3(sK2,sK4) = sK3
% 1.18/0.99      | sK3 != X0_51 ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_734]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_903,plain,
% 1.18/0.99      ( k16_lattice3(sK2,sK4) != k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
% 1.18/0.99      | k16_lattice3(sK2,sK4) = sK3
% 1.18/0.99      | sK3 != k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_849]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_861,plain,
% 1.18/0.99      ( X0_51 != X1_51
% 1.18/0.99      | k16_lattice3(sK2,sK4) != X1_51
% 1.18/0.99      | k16_lattice3(sK2,sK4) = X0_51 ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_734]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_880,plain,
% 1.18/0.99      ( X0_51 != k16_lattice3(sK2,sK4)
% 1.18/0.99      | k16_lattice3(sK2,sK4) = X0_51
% 1.18/0.99      | k16_lattice3(sK2,sK4) != k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_861]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_896,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) != k16_lattice3(sK2,sK4)
% 1.18/0.99      | k16_lattice3(sK2,sK4) = k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
% 1.18/0.99      | k16_lattice3(sK2,sK4) != k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_880]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_733,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_860,plain,
% 1.18/0.99      ( k16_lattice3(sK2,sK4) = k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_733]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_17,plain,
% 1.18/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 1.18/0.99      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.99      | ~ v4_lattice3(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0) ),
% 1.18/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_19,negated_conjecture,
% 1.18/0.99      ( r3_lattice3(sK2,sK3,sK4) ),
% 1.18/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_270,plain,
% 1.18/0.99      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.99      | ~ v4_lattice3(X0)
% 1.18/0.99      | ~ l3_lattices(X0)
% 1.18/0.99      | v2_struct_0(X0)
% 1.18/0.99      | ~ v10_lattices(X0)
% 1.18/0.99      | sK3 != X1
% 1.18/0.99      | sK4 != X2
% 1.18/0.99      | sK2 != X0 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_271,plain,
% 1.18/0.99      ( r3_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.18/0.99      | ~ v4_lattice3(sK2)
% 1.18/0.99      | ~ l3_lattices(sK2)
% 1.18/0.99      | v2_struct_0(sK2)
% 1.18/0.99      | ~ v10_lattices(sK2) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_270]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_273,plain,
% 1.18/0.99      ( r3_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_271,c_25,c_24,c_23,c_22,c_21]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_508,plain,
% 1.18/0.99      ( r1_lattices(sK2,X0,X1)
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | k16_lattice3(sK2,sK4) != X1
% 1.18/0.99      | sK3 != X0
% 1.18/0.99      | sK2 != sK2 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_273,c_429]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_509,plain,
% 1.18/0.99      ( r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
% 1.18/0.99      | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_508]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_511,plain,
% 1.18/0.99      ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_509,c_21]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_512,plain,
% 1.18/0.99      ( r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4))
% 1.18/0.99      | ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
% 1.18/0.99      inference(renaming,[status(thm)],[c_511]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_519,plain,
% 1.18/0.99      ( r1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) ),
% 1.18/0.99      inference(forward_subsumption_resolution,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_512,c_486]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_647,plain,
% 1.18/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,X1,X0) = X0
% 1.18/0.99      | k16_lattice3(sK2,sK4) != X0
% 1.18/0.99      | sK3 != X1
% 1.18/0.99      | sK2 != sK2 ),
% 1.18/0.99      inference(resolution_lifted,[status(thm)],[c_569,c_519]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_648,plain,
% 1.18/0.99      ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_650,plain,
% 1.18/0.99      ( ~ m1_subset_1(k16_lattice3(sK2,sK4),u1_struct_0(sK2))
% 1.18/0.99      | k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(global_propositional_subsumption,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_648,c_21]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_658,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(forward_subsumption_resolution,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_650,c_486]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_727,plain,
% 1.18/0.99      ( k1_lattices(sK2,sK3,k16_lattice3(sK2,sK4)) = k16_lattice3(sK2,sK4) ),
% 1.18/0.99      inference(subtyping,[status(esa)],[c_658]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_18,negated_conjecture,
% 1.18/0.99      ( k16_lattice3(sK2,sK4) != sK3 ),
% 1.18/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_731,negated_conjecture,
% 1.18/0.99      ( k16_lattice3(sK2,sK4) != sK3 ),
% 1.18/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(c_740,plain,
% 1.18/0.99      ( sK3 = sK3 ),
% 1.18/0.99      inference(instantiation,[status(thm)],[c_733]) ).
% 1.18/0.99  
% 1.18/0.99  cnf(contradiction,plain,
% 1.18/0.99      ( $false ),
% 1.18/0.99      inference(minisat,
% 1.18/0.99                [status(thm)],
% 1.18/0.99                [c_975,c_942,c_903,c_896,c_860,c_727,c_731,c_740]) ).
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  ------                               Statistics
% 1.18/0.99  
% 1.18/0.99  ------ General
% 1.18/0.99  
% 1.18/0.99  abstr_ref_over_cycles:                  0
% 1.18/0.99  abstr_ref_under_cycles:                 0
% 1.18/0.99  gc_basic_clause_elim:                   0
% 1.18/0.99  forced_gc_time:                         0
% 1.18/0.99  parsing_time:                           0.013
% 1.18/0.99  unif_index_cands_time:                  0.
% 1.18/0.99  unif_index_add_time:                    0.
% 1.18/0.99  orderings_time:                         0.
% 1.18/0.99  out_proof_time:                         0.017
% 1.18/0.99  total_time:                             0.079
% 1.18/0.99  num_of_symbols:                         55
% 1.18/0.99  num_of_terms:                           748
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing
% 1.18/0.99  
% 1.18/0.99  num_of_splits:                          0
% 1.18/0.99  num_of_split_atoms:                     0
% 1.18/0.99  num_of_reused_defs:                     0
% 1.18/0.99  num_eq_ax_congr_red:                    21
% 1.18/0.99  num_of_sem_filtered_clauses:            1
% 1.18/0.99  num_of_subtypes:                        4
% 1.18/0.99  monotx_restored_types:                  0
% 1.18/0.99  sat_num_of_epr_types:                   0
% 1.18/0.99  sat_num_of_non_cyclic_types:            0
% 1.18/0.99  sat_guarded_non_collapsed_types:        0
% 1.18/0.99  num_pure_diseq_elim:                    0
% 1.18/0.99  simp_replaced_by:                       0
% 1.18/0.99  res_preprocessed:                       55
% 1.18/0.99  prep_upred:                             0
% 1.18/0.99  prep_unflattend:                        35
% 1.18/0.99  smt_new_axioms:                         0
% 1.18/0.99  pred_elim_cands:                        1
% 1.18/0.99  pred_elim:                              13
% 1.18/0.99  pred_elim_cl:                           18
% 1.18/0.99  pred_elim_cycles:                       15
% 1.18/0.99  merged_defs:                            0
% 1.18/0.99  merged_defs_ncl:                        0
% 1.18/0.99  bin_hyper_res:                          0
% 1.18/0.99  prep_cycles:                            4
% 1.18/0.99  pred_elim_time:                         0.008
% 1.18/0.99  splitting_time:                         0.
% 1.18/0.99  sem_filter_time:                        0.
% 1.18/0.99  monotx_time:                            0.
% 1.18/0.99  subtype_inf_time:                       0.
% 1.18/0.99  
% 1.18/0.99  ------ Problem properties
% 1.18/0.99  
% 1.18/0.99  clauses:                                7
% 1.18/0.99  conjectures:                            2
% 1.18/0.99  epr:                                    0
% 1.18/0.99  horn:                                   7
% 1.18/0.99  ground:                                 5
% 1.18/0.99  unary:                                  5
% 1.18/0.99  binary:                                 1
% 1.18/0.99  lits:                                   10
% 1.18/0.99  lits_eq:                                5
% 1.18/0.99  fd_pure:                                0
% 1.18/0.99  fd_pseudo:                              0
% 1.18/0.99  fd_cond:                                0
% 1.18/0.99  fd_pseudo_cond:                         0
% 1.18/0.99  ac_symbols:                             0
% 1.18/0.99  
% 1.18/0.99  ------ Propositional Solver
% 1.18/0.99  
% 1.18/0.99  prop_solver_calls:                      26
% 1.18/0.99  prop_fast_solver_calls:                 440
% 1.18/0.99  smt_solver_calls:                       0
% 1.18/0.99  smt_fast_solver_calls:                  0
% 1.18/0.99  prop_num_of_clauses:                    277
% 1.18/0.99  prop_preprocess_simplified:             1352
% 1.18/0.99  prop_fo_subsumed:                       40
% 1.18/0.99  prop_solver_time:                       0.
% 1.18/0.99  smt_solver_time:                        0.
% 1.18/0.99  smt_fast_solver_time:                   0.
% 1.18/0.99  prop_fast_solver_time:                  0.
% 1.18/0.99  prop_unsat_core_time:                   0.
% 1.18/0.99  
% 1.18/0.99  ------ QBF
% 1.18/0.99  
% 1.18/0.99  qbf_q_res:                              0
% 1.18/0.99  qbf_num_tautologies:                    0
% 1.18/0.99  qbf_prep_cycles:                        0
% 1.18/0.99  
% 1.18/0.99  ------ BMC1
% 1.18/0.99  
% 1.18/0.99  bmc1_current_bound:                     -1
% 1.18/0.99  bmc1_last_solved_bound:                 -1
% 1.18/0.99  bmc1_unsat_core_size:                   -1
% 1.18/0.99  bmc1_unsat_core_parents_size:           -1
% 1.18/0.99  bmc1_merge_next_fun:                    0
% 1.18/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.18/0.99  
% 1.18/0.99  ------ Instantiation
% 1.18/0.99  
% 1.18/0.99  inst_num_of_clauses:                    44
% 1.18/0.99  inst_num_in_passive:                    1
% 1.18/0.99  inst_num_in_active:                     36
% 1.18/0.99  inst_num_in_unprocessed:                7
% 1.18/0.99  inst_num_of_loops:                      40
% 1.18/0.99  inst_num_of_learning_restarts:          0
% 1.18/0.99  inst_num_moves_active_passive:          0
% 1.18/0.99  inst_lit_activity:                      0
% 1.18/0.99  inst_lit_activity_moves:                0
% 1.18/0.99  inst_num_tautologies:                   0
% 1.18/0.99  inst_num_prop_implied:                  0
% 1.18/0.99  inst_num_existing_simplified:           0
% 1.18/0.99  inst_num_eq_res_simplified:             0
% 1.18/0.99  inst_num_child_elim:                    0
% 1.18/1.00  inst_num_of_dismatching_blockings:      0
% 1.18/1.00  inst_num_of_non_proper_insts:           36
% 1.18/1.00  inst_num_of_duplicates:                 0
% 1.18/1.00  inst_inst_num_from_inst_to_res:         0
% 1.18/1.00  inst_dismatching_checking_time:         0.
% 1.18/1.00  
% 1.18/1.00  ------ Resolution
% 1.18/1.00  
% 1.18/1.00  res_num_of_clauses:                     0
% 1.18/1.00  res_num_in_passive:                     0
% 1.18/1.00  res_num_in_active:                      0
% 1.18/1.00  res_num_of_loops:                       59
% 1.18/1.00  res_forward_subset_subsumed:            8
% 1.18/1.00  res_backward_subset_subsumed:           0
% 1.18/1.00  res_forward_subsumed:                   0
% 1.18/1.00  res_backward_subsumed:                  0
% 1.18/1.00  res_forward_subsumption_resolution:     4
% 1.18/1.00  res_backward_subsumption_resolution:    0
% 1.18/1.00  res_clause_to_clause_subsumption:       29
% 1.18/1.00  res_orphan_elimination:                 0
% 1.18/1.00  res_tautology_del:                      12
% 1.18/1.00  res_num_eq_res_simplified:              0
% 1.18/1.00  res_num_sel_changes:                    0
% 1.18/1.00  res_moves_from_active_to_pass:          0
% 1.18/1.00  
% 1.18/1.00  ------ Superposition
% 1.18/1.00  
% 1.18/1.00  sup_time_total:                         0.
% 1.18/1.00  sup_time_generating:                    0.
% 1.18/1.00  sup_time_sim_full:                      0.
% 1.18/1.00  sup_time_sim_immed:                     0.
% 1.18/1.00  
% 1.18/1.00  sup_num_of_clauses:                     11
% 1.18/1.00  sup_num_in_active:                      8
% 1.18/1.00  sup_num_in_passive:                     3
% 1.18/1.00  sup_num_of_loops:                       7
% 1.18/1.00  sup_fw_superposition:                   5
% 1.18/1.00  sup_bw_superposition:                   1
% 1.18/1.00  sup_immediate_simplified:               0
% 1.18/1.00  sup_given_eliminated:                   0
% 1.18/1.00  comparisons_done:                       0
% 1.18/1.00  comparisons_avoided:                    0
% 1.18/1.00  
% 1.18/1.00  ------ Simplifications
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  sim_fw_subset_subsumed:                 0
% 1.18/1.00  sim_bw_subset_subsumed:                 0
% 1.18/1.00  sim_fw_subsumed:                        0
% 1.18/1.00  sim_bw_subsumed:                        0
% 1.18/1.00  sim_fw_subsumption_res:                 0
% 1.18/1.00  sim_bw_subsumption_res:                 0
% 1.18/1.00  sim_tautology_del:                      0
% 1.18/1.00  sim_eq_tautology_del:                   1
% 1.18/1.00  sim_eq_res_simp:                        0
% 1.18/1.00  sim_fw_demodulated:                     0
% 1.18/1.00  sim_bw_demodulated:                     0
% 1.18/1.00  sim_light_normalised:                   0
% 1.18/1.00  sim_joinable_taut:                      0
% 1.18/1.00  sim_joinable_simp:                      0
% 1.18/1.00  sim_ac_normalised:                      0
% 1.18/1.00  sim_smt_subsumption:                    0
% 1.18/1.00  
%------------------------------------------------------------------------------

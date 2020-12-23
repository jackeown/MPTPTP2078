%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1196+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:07 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 245 expanded)
%              Number of clauses        :   53 (  66 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  416 (1554 expanded)
%              Number of equality atoms :   87 (  92 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) != k1_lattices(X0,k1_lattices(X0,X1,X2),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3)) != k1_lattices(X0,k1_lattices(X0,X1,sK1(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k1_lattices(X0,sK0(X0),X2),X3) != k1_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,k1_lattices(X0,sK0(X0),sK1(X0)),sK2(X0)) != k1_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f33,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,sK5))
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_lattices(X0,sK4,k1_lattices(X0,sK4,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK3,X1,k1_lattices(sK3,X1,X2))
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v9_lattices(sK3)
      & v8_lattices(sK3)
      & v6_lattices(sK3)
      & v5_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v9_lattices(sK3)
    & v8_lattices(sK3)
    & v6_lattices(sK3)
    & v5_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f29,f28,f27])).

fof(f46,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v5_lattices(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ~ r1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    v9_lattices(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v6_lattices(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v8_lattices(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_359,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1152,plain,
    ( k1_lattices(sK3,sK4,sK4) != X0_45
    | sK4 != X0_45
    | sK4 = k1_lattices(sK3,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1153,plain,
    ( k1_lattices(sK3,sK4,sK4) != sK4
    | sK4 = k1_lattices(sK3,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_360,plain,
    ( X0_45 != X1_45
    | X2_45 != X3_45
    | k1_lattices(X0_47,X0_45,X2_45) = k1_lattices(X0_47,X1_45,X3_45) ),
    theory(equality)).

cnf(c_566,plain,
    ( k1_lattices(sK3,sK4,sK5) = k1_lattices(sK3,X0_45,X1_45)
    | sK5 != X1_45
    | sK4 != X0_45 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_581,plain,
    ( k1_lattices(sK3,sK4,sK5) = k1_lattices(sK3,X0_45,sK5)
    | sK5 != sK5
    | sK4 != X0_45 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_701,plain,
    ( k1_lattices(sK3,sK4,sK5) = k1_lattices(sK3,k1_lattices(sK3,sK4,sK4),sK5)
    | sK5 != sK5
    | sK4 != k1_lattices(sK3,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,k1_lattices(X1,X3,X2),X0) = k1_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_218,plain,
    ( l2_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_219,plain,
    ( l2_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X3,k1_lattices(X1,X2,X0)) = k1_lattices(X1,k1_lattices(X1,X3,X2),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_219])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v5_lattices(sK3)
    | v2_struct_0(sK3)
    | k1_lattices(sK3,X2,k1_lattices(sK3,X1,X0)) = k1_lattices(sK3,k1_lattices(sK3,X2,X1),X0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( v5_lattices(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k1_lattices(sK3,X2,k1_lattices(sK3,X1,X0)) = k1_lattices(sK3,k1_lattices(sK3,X2,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_18,c_17])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k1_lattices(sK3,X1,k1_lattices(sK3,X2,X0)) = k1_lattices(sK3,k1_lattices(sK3,X1,X2),X0) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_45,u1_struct_0(sK3))
    | k1_lattices(sK3,X1_45,k1_lattices(sK3,X2_45,X0_45)) = k1_lattices(sK3,k1_lattices(sK3,X1_45,X2_45),X0_45) ),
    inference(subtyping,[status(esa)],[c_280])).

cnf(c_621,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) = k1_lattices(sK3,k1_lattices(sK3,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_545,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != X0_45
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) = k1_lattices(sK3,sK4,sK5)
    | k1_lattices(sK3,sK4,sK5) != X0_45 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_565,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != k1_lattices(sK3,X0_45,X1_45)
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) = k1_lattices(sK3,sK4,sK5)
    | k1_lattices(sK3,sK4,sK5) != k1_lattices(sK3,X0_45,X1_45) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_614,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != k1_lattices(sK3,X0_45,sK5)
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) = k1_lattices(sK3,sK4,sK5)
    | k1_lattices(sK3,sK4,sK5) != k1_lattices(sK3,X0_45,sK5) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_620,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != k1_lattices(sK3,k1_lattices(sK3,sK4,sK4),sK5)
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) = k1_lattices(sK3,sK4,sK5)
    | k1_lattices(sK3,sK4,sK5) != k1_lattices(sK3,k1_lattices(sK3,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_358,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_582,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_219])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k1_lattices(sK3,X1,X0),u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( m1_subset_1(k1_lattices(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_18])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k1_lattices(sK3,X1,X0),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3))
    | m1_subset_1(k1_lattices(sK3,X1_45,X0_45),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_518,plain,
    ( m1_subset_1(k1_lattices(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_0,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( ~ r1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,X2,X0) != X0
    | k1_lattices(sK3,sK4,sK5) != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_229,plain,
    ( ~ m1_subset_1(k1_lattices(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l2_lattices(sK3)
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != k1_lattices(sK3,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32,plain,
    ( ~ l3_lattices(sK3)
    | l2_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_231,plain,
    ( ~ m1_subset_1(k1_lattices(sK3,sK4,sK5),u1_struct_0(sK3))
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != k1_lattices(sK3,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_18,c_13,c_12,c_32])).

cnf(c_353,plain,
    ( ~ m1_subset_1(k1_lattices(sK3,sK4,sK5),u1_struct_0(sK3))
    | k1_lattices(sK3,sK4,k1_lattices(sK3,sK4,sK5)) != k1_lattices(sK3,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_231])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( v9_lattices(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v6_lattices(sK3)
    | ~ v8_lattices(sK3)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | k1_lattices(sK3,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_16,negated_conjecture,
    ( v6_lattices(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( v8_lattices(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_lattices(sK3,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_198,c_18,c_16,c_15,c_13])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | k1_lattices(sK3,X0_45,X0_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_369,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k1_lattices(sK3,sK4,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_365,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1153,c_701,c_621,c_620,c_582,c_518,c_353,c_369,c_365,c_11,c_12])).


%------------------------------------------------------------------------------

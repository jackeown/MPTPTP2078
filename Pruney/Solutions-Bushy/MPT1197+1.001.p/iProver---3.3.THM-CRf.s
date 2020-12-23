%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1197+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:07 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 451 expanded)
%              Number of clauses        :   67 ( 120 expanded)
%              Number of leaves         :   14 ( 141 expanded)
%              Depth                    :   16
%              Number of atoms          :  443 (2422 expanded)
%              Number of equality atoms :   99 ( 129 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,k4_lattices(X0,X1,sK4),X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_lattices(X0,k4_lattices(X0,sK3,X2),sK3)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK2,k4_lattices(sK2,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v8_lattices(sK2)
      & v6_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v8_lattices(sK2)
    & v6_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f30,f29,f28])).

fof(f47,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    v6_lattices(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0)
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f35,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    v8_lattices(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ~ r1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_460,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_595,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_461,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_594,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_16,negated_conjecture,
    ( v6_lattices(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_lattices(sK2)
    | k4_lattices(sK2,X0,X1) = k4_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ l3_lattices(X0)
    | l1_lattices(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,plain,
    ( ~ l3_lattices(sK2)
    | l1_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,X0,X1) = k4_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_215,c_17,c_14,c_29])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | k4_lattices(sK2,X0_45,X1_45) = k4_lattices(sK2,X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_597,plain,
    ( k4_lattices(sK2,X0_45,X1_45) = k4_lattices(sK2,X1_45,X0_45)
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_905,plain,
    ( k4_lattices(sK2,X0_45,sK4) = k4_lattices(sK2,sK4,X0_45)
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_597])).

cnf(c_979,plain,
    ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_595,c_905])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_lattices(sK2)
    | k2_lattices(sK2,X0,X1) = k4_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = k4_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_194,c_17,c_14,c_29])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | k2_lattices(sK2,X0_45,X1_45) = k4_lattices(sK2,X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_596,plain,
    ( k2_lattices(sK2,X0_45,X1_45) = k4_lattices(sK2,X0_45,X1_45)
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_691,plain,
    ( k2_lattices(sK2,sK4,X0_45) = k4_lattices(sK2,sK4,X0_45)
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_596])).

cnf(c_783,plain,
    ( k2_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_595,c_691])).

cnf(c_1028,plain,
    ( k2_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_979,c_783])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | ~ v8_lattices(sK2)
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_15,negated_conjecture,
    ( v8_lattices(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_15,c_14])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0_45,X1_45),X1_45) = X1_45 ),
    inference(subtyping,[status(esa)],[c_380])).

cnf(c_600,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,X0_45,X1_45),X1_45) = X1_45
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_1199,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK4,X0_45),X0_45) = X0_45
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_600])).

cnf(c_1324,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK4,sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_595,c_1199])).

cnf(c_1435,plain,
    ( k1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_1028,c_1324])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_7])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_17])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k2_lattices(sK2,X0,X1),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( m1_subset_1(k2_lattices(sK2,X0,X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_14])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k2_lattices(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | m1_subset_1(k2_lattices(sK2,X0_45,X1_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_1048,plain,
    ( m1_subset_1(k2_lattices(sK2,sK4,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(X1_45,X0_46)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_654,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_lattices(sK2,X1_45,X2_45),u1_struct_0(sK2))
    | X0_45 != k2_lattices(sK2,X1_45,X2_45) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_671,plain,
    ( ~ m1_subset_1(k2_lattices(sK2,X0_45,X1_45),u1_struct_0(sK2))
    | m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2))
    | k4_lattices(sK2,sK3,sK4) != k2_lattices(sK2,X0_45,X1_45) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_860,plain,
    ( ~ m1_subset_1(k2_lattices(sK2,sK4,sK3),u1_struct_0(sK2))
    | m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2))
    | k4_lattices(sK2,sK3,sK4) != k2_lattices(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_464,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_714,plain,
    ( X0_45 != X1_45
    | k4_lattices(sK2,sK3,sK4) != X1_45
    | k4_lattices(sK2,sK3,sK4) = X0_45 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_757,plain,
    ( X0_45 != k4_lattices(sK2,sK4,sK3)
    | k4_lattices(sK2,sK3,sK4) = X0_45
    | k4_lattices(sK2,sK3,sK4) != k4_lattices(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_829,plain,
    ( k2_lattices(sK2,sK4,sK3) != k4_lattices(sK2,sK4,sK3)
    | k4_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK4,sK3)
    | k4_lattices(sK2,sK3,sK4) != k4_lattices(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_708,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_702,plain,
    ( k2_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK4,sK3)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_8,plain,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_293,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_11,negated_conjecture,
    ( ~ r1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) != X0
    | k4_lattices(sK2,sK3,sK4) != X2
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_293,c_11])).

cnf(c_332,plain,
    ( ~ m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_334,plain,
    ( ~ m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2))
    | k1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_17,c_14,c_13])).

cnf(c_457,plain,
    ( ~ m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2))
    | k1_lattices(sK2,k4_lattices(sK2,sK3,sK4),sK3) != sK3 ),
    inference(subtyping,[status(esa)],[c_334])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1435,c_1048,c_860,c_829,c_708,c_702,c_457,c_12,c_22,c_13])).


%------------------------------------------------------------------------------

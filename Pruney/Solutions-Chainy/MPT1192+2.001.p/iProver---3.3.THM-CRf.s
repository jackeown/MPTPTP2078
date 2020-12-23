%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:11 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 579 expanded)
%              Number of clauses        :   73 ( 174 expanded)
%              Number of leaves         :   13 ( 146 expanded)
%              Depth                    :   20
%              Number of atoms          :  489 (3069 expanded)
%              Number of equality atoms :  139 ( 561 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK5,sK5) != sK5
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_lattices(X0,X1,X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_lattices(sK4,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v9_lattices(sK4)
      & v8_lattices(sK4)
      & v6_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_lattices(sK4,sK5,sK5) != sK5
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v9_lattices(sK4)
    & v8_lattices(sK4)
    & v6_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f46,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    v6_lattices(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK3(X0))) != X1
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) != sK2(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != sK2(X0)
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).

fof(f40,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v9_lattices(sK4) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    v8_lattices(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    k1_lattices(sK4,sK5,sK5) != sK5 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_633,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_753,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_10,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_9])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_19])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k1_lattices(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_15,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_522,plain,
    ( m1_subset_1(k1_lattices(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_15])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k1_lattices(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_522])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | m1_subset_1(k1_lattices(sK4,X0_46,X1_46),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_523])).

cnf(c_758,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_lattices(sK4,X0_46,X1_46),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( v6_lattices(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_lattices(sK4)
    | k2_lattices(sK4,X0,X1) = k4_lattices(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_11,plain,
    ( ~ l3_lattices(X0)
    | l1_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( ~ l3_lattices(sK4)
    | l1_lattices(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k2_lattices(sK4,X0,X1) = k4_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_19,c_15,c_30])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | k2_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_754,plain,
    ( k2_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X0_46,X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1267,plain,
    ( k2_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),X2_46) = k4_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),X2_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_754])).

cnf(c_5000,plain,
    ( k2_lattices(sK4,k1_lattices(sK4,sK5,X0_46),X1_46) = k4_lattices(sK4,k1_lattices(sK4,sK5,X0_46),X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_1267])).

cnf(c_5210,plain,
    ( k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),X0_46) = k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_5000])).

cnf(c_5231,plain,
    ( k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) ),
    inference(superposition,[status(thm)],[c_753,c_5210])).

cnf(c_837,plain,
    ( k2_lattices(sK4,sK5,X0_46) = k4_lattices(sK4,sK5,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_754])).

cnf(c_1266,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,X0_46,X1_46)) = k4_lattices(sK4,sK5,k1_lattices(sK4,X0_46,X1_46))
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_837])).

cnf(c_2168,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46)) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_1266])).

cnf(c_2189,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_753,c_2168])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v9_lattices(sK4)
    | ~ l3_lattices(sK4)
    | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_16,negated_conjecture,
    ( v9_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_19,c_15,c_464])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | k2_lattices(sK4,X0_46,k1_lattices(sK4,X0_46,X1_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_541])).

cnf(c_757,plain,
    ( k2_lattices(sK4,X0_46,k1_lattices(sK4,X0_46,X1_46)) = X0_46
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1164,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46)) = sK5
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_757])).

cnf(c_1169,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_753,c_1164])).

cnf(c_2198,plain,
    ( k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_2189,c_1169])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_lattices(sK4)
    | k4_lattices(sK4,X0,X1) = k4_lattices(sK4,X1,X0) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k4_lattices(sK4,X0,X1) = k4_lattices(sK4,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_19,c_15,c_30])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | k4_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_253])).

cnf(c_755,plain,
    ( k4_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X1_46,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_901,plain,
    ( k4_lattices(sK4,X0_46,sK5) = k4_lattices(sK4,sK5,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_755])).

cnf(c_1264,plain,
    ( k4_lattices(sK4,sK5,k1_lattices(sK4,X0_46,X1_46)) = k4_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),sK5)
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_901])).

cnf(c_1535,plain,
    ( k4_lattices(sK4,k1_lattices(sK4,sK5,X0_46),sK5) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_1264])).

cnf(c_1695,plain,
    ( k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_753,c_1535])).

cnf(c_2325,plain,
    ( k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_2198,c_1695])).

cnf(c_5240,plain,
    ( k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_5231,c_2325])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | ~ v8_lattices(sK4)
    | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_17,negated_conjecture,
    ( v8_lattices(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_19,c_15,c_350])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
    | k1_lattices(sK4,k2_lattices(sK4,X0_46,X1_46),X1_46) = X1_46 ),
    inference(subtyping,[status(esa)],[c_558])).

cnf(c_756,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,X0_46,X1_46),X1_46) = X1_46
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1263,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),X2_46),X2_46) = X2_46
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_756])).

cnf(c_2866,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,sK5,X0_46),X1_46),X1_46) = X1_46
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_1263])).

cnf(c_3112,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),X0_46),X0_46) = X0_46
    | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_2866])).

cnf(c_3133,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_753,c_3112])).

cnf(c_5418,plain,
    ( k1_lattices(sK4,sK5,sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_5240,c_3133])).

cnf(c_13,negated_conjecture,
    ( k1_lattices(sK4,sK5,sK5) != sK5 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_634,negated_conjecture,
    ( k1_lattices(sK4,sK5,sK5) != sK5 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5418,c_634])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:06:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.99  
% 3.18/0.99  ------  iProver source info
% 3.18/0.99  
% 3.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.99  git: non_committed_changes: false
% 3.18/0.99  git: last_make_outside_of_git: false
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  ------ Parsing...
% 3.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.99  ------ Proving...
% 3.18/0.99  ------ Problem Properties 
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  clauses                                 7
% 3.18/0.99  conjectures                             2
% 3.18/0.99  EPR                                     0
% 3.18/0.99  Horn                                    7
% 3.18/0.99  unary                                   2
% 3.18/0.99  binary                                  0
% 3.18/0.99  lits                                    17
% 3.18/0.99  lits eq                                 5
% 3.18/0.99  fd_pure                                 0
% 3.18/0.99  fd_pseudo                               0
% 3.18/0.99  fd_cond                                 0
% 3.18/0.99  fd_pseudo_cond                          0
% 3.18/0.99  AC symbols                              0
% 3.18/0.99  
% 3.18/0.99  ------ Schedule dynamic 5 is on 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  Current options:
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     none
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       false
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ Proving...
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS status Theorem for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  fof(f7,conjecture,(
% 3.18/0.99    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f8,negated_conjecture,(
% 3.18/1.00    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.18/1.00    inference(negated_conjecture,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f20,plain,(
% 3.18/1.00    ? [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ? [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))),
% 3.18/1.00    inference(flattening,[],[f20])).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    ( ! [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) => (k1_lattices(X0,sK5,sK5) != sK5 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f32,plain,(
% 3.18/1.00    ? [X0] : (? [X1] : (k1_lattices(X0,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_lattices(sK4,X1,X1) != X1 & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v9_lattices(sK4) & v8_lattices(sK4) & v6_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    (k1_lattices(sK4,sK5,sK5) != sK5 & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v9_lattices(sK4) & v8_lattices(sK4) & v6_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f33,f32])).
% 3.18/1.00  
% 3.18/1.00  fof(f53,plain,(
% 3.18/1.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f17,plain,(
% 3.18/1.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.18/1.00    inference(ennf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f46,plain,(
% 3.18/1.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f15,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f16,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(flattening,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f44,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f48,plain,(
% 3.18/1.00    ~v2_struct_0(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f52,plain,(
% 3.18/1.00    l3_lattices(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f18,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f19,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(flattening,[],[f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f47,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f49,plain,(
% 3.18/1.00    v6_lattices(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f45,plain,(
% 3.18/1.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f13,plain,(
% 3.18/1.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f14,plain,(
% 3.18/1.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(flattening,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f27,plain,(
% 3.18/1.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(nnf_transformation,[],[f14])).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(rectify,[],[f27])).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK3(X0))) != X1 & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) != sK2(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f31,plain,(
% 3.18/1.00    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != sK2(X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f40,plain,(
% 3.18/1.00    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f51,plain,(
% 3.18/1.00    v9_lattices(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f1,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f9,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f1])).
% 3.18/1.00  
% 3.18/1.00  fof(f10,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(flattening,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f35,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f2,axiom,(
% 3.18/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f11,plain,(
% 3.18/1.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f2])).
% 3.18/1.00  
% 3.18/1.00  fof(f12,plain,(
% 3.18/1.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(flattening,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(nnf_transformation,[],[f12])).
% 3.18/1.00  
% 3.18/1.00  fof(f23,plain,(
% 3.18/1.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(rectify,[],[f22])).
% 3.18/1.00  
% 3.18/1.00  fof(f25,plain,(
% 3.18/1.00    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f24,plain,(
% 3.18/1.00    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f26,plain,(
% 3.18/1.00    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f26])).
% 3.18/1.00  
% 3.18/1.00  fof(f50,plain,(
% 3.18/1.00    v8_lattices(sK4)),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f54,plain,(
% 3.18/1.00    k1_lattices(sK4,sK5,sK5) != sK5),
% 3.18/1.00    inference(cnf_transformation,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_14,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_633,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_753,plain,
% 3.18/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10,plain,
% 3.18/1.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.18/1.00      | ~ l2_lattices(X1)
% 3.18/1.00      | v2_struct_0(X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_200,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X3)
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | X1 != X3 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_201,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | v2_struct_0(X1) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_200]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_19,negated_conjecture,
% 3.18/1.00      ( ~ v2_struct_0(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_517,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | m1_subset_1(k1_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_201,c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_518,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | m1_subset_1(k1_lattices(sK4,X0,X1),u1_struct_0(sK4))
% 3.18/1.00      | ~ l3_lattices(sK4) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_517]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15,negated_conjecture,
% 3.18/1.00      ( l3_lattices(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_522,plain,
% 3.18/1.00      ( m1_subset_1(k1_lattices(sK4,X0,X1),u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_518,c_15]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_523,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | m1_subset_1(k1_lattices(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_522]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_628,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 3.18/1.00      | m1_subset_1(k1_lattices(sK4,X0_46,X1_46),u1_struct_0(sK4)) ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_523]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_758,plain,
% 3.18/1.00      ( m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(k1_lattices(sK4,X0_46,X1_46),u1_struct_0(sK4)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | ~ v6_lattices(X1)
% 3.18/1.00      | ~ l1_lattices(X1)
% 3.18/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_18,negated_conjecture,
% 3.18/1.00      ( v6_lattices(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_227,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | ~ l1_lattices(X1)
% 3.18/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_228,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | v2_struct_0(sK4)
% 3.18/1.00      | ~ l1_lattices(sK4)
% 3.18/1.00      | k2_lattices(sK4,X0,X1) = k4_lattices(sK4,X0,X1) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_227]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_11,plain,
% 3.18/1.00      ( ~ l3_lattices(X0) | l1_lattices(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_30,plain,
% 3.18/1.00      ( ~ l3_lattices(sK4) | l1_lattices(sK4) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_232,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | k2_lattices(sK4,X0,X1) = k4_lattices(sK4,X0,X1) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_228,c_19,c_15,c_30]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_632,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 3.18/1.00      | k2_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X0_46,X1_46) ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_232]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_754,plain,
% 3.18/1.00      ( k2_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X0_46,X1_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1267,plain,
% 3.18/1.00      ( k2_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),X2_46) = k4_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),X2_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X2_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_758,c_754]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5000,plain,
% 3.18/1.00      ( k2_lattices(sK4,k1_lattices(sK4,sK5,X0_46),X1_46) = k4_lattices(sK4,k1_lattices(sK4,sK5,X0_46),X1_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_1267]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5210,plain,
% 3.18/1.00      ( k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),X0_46) = k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),X0_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_5000]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5231,plain,
% 3.18/1.00      ( k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_5210]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_837,plain,
% 3.18/1.00      ( k2_lattices(sK4,sK5,X0_46) = k4_lattices(sK4,sK5,X0_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_754]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1266,plain,
% 3.18/1.00      ( k2_lattices(sK4,sK5,k1_lattices(sK4,X0_46,X1_46)) = k4_lattices(sK4,sK5,k1_lattices(sK4,X0_46,X1_46))
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_758,c_837]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2168,plain,
% 3.18/1.00      ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46)) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46))
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_1266]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2189,plain,
% 3.18/1.00      ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_2168]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | ~ v9_lattices(X1)
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_538,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | ~ v9_lattices(X1)
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_539,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | ~ v9_lattices(sK4)
% 3.18/1.00      | ~ l3_lattices(sK4)
% 3.18/1.00      | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_538]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_16,negated_conjecture,
% 3.18/1.00      ( v9_lattices(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_463,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_464,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | ~ l3_lattices(sK4)
% 3.18/1.00      | v2_struct_0(sK4)
% 3.18/1.00      | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_463]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_541,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_539,c_19,c_15,c_464]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_629,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 3.18/1.00      | k2_lattices(sK4,X0_46,k1_lattices(sK4,X0_46,X1_46)) = X0_46 ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_541]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_757,plain,
% 3.18/1.00      ( k2_lattices(sK4,X0_46,k1_lattices(sK4,X0_46,X1_46)) = X0_46
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1164,plain,
% 3.18/1.00      ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46)) = sK5
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_757]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1169,plain,
% 3.18/1.00      ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) = sK5 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_1164]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2198,plain,
% 3.18/1.00      ( k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) = sK5 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_2189,c_1169]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_0,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | ~ v6_lattices(X1)
% 3.18/1.00      | ~ l1_lattices(X1)
% 3.18/1.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_248,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | ~ l1_lattices(X1)
% 3.18/1.00      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_249,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | v2_struct_0(sK4)
% 3.18/1.00      | ~ l1_lattices(sK4)
% 3.18/1.00      | k4_lattices(sK4,X0,X1) = k4_lattices(sK4,X1,X0) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_248]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_253,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | k4_lattices(sK4,X0,X1) = k4_lattices(sK4,X1,X0) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_249,c_19,c_15,c_30]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_631,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 3.18/1.00      | k4_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X1_46,X0_46) ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_253]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_755,plain,
% 3.18/1.00      ( k4_lattices(sK4,X0_46,X1_46) = k4_lattices(sK4,X1_46,X0_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_901,plain,
% 3.18/1.00      ( k4_lattices(sK4,X0_46,sK5) = k4_lattices(sK4,sK5,X0_46)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_755]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1264,plain,
% 3.18/1.00      ( k4_lattices(sK4,sK5,k1_lattices(sK4,X0_46,X1_46)) = k4_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),sK5)
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_758,c_901]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1535,plain,
% 3.18/1.00      ( k4_lattices(sK4,k1_lattices(sK4,sK5,X0_46),sK5) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_46))
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_1264]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1695,plain,
% 3.18/1.00      ( k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = k4_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK5)) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_1535]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2325,plain,
% 3.18/1.00      ( k4_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = sK5 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_2198,c_1695]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5240,plain,
% 3.18/1.00      ( k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5) = sK5 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_5231,c_2325]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | ~ v8_lattices(X1)
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_555,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | ~ v8_lattices(X1)
% 3.18/1.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_556,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | ~ l3_lattices(sK4)
% 3.18/1.00      | ~ v8_lattices(sK4)
% 3.18/1.00      | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_555]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_17,negated_conjecture,
% 3.18/1.00      ( v8_lattices(sK4) ),
% 3.18/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_349,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.18/1.00      | ~ l3_lattices(X1)
% 3.18/1.00      | v2_struct_0(X1)
% 3.18/1.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.18/1.00      | sK4 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_350,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | ~ l3_lattices(sK4)
% 3.18/1.00      | v2_struct_0(sK4)
% 3.18/1.00      | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_558,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.18/1.00      | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_556,c_19,c_15,c_350]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_630,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK4))
% 3.18/1.00      | ~ m1_subset_1(X1_46,u1_struct_0(sK4))
% 3.18/1.00      | k1_lattices(sK4,k2_lattices(sK4,X0_46,X1_46),X1_46) = X1_46 ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_558]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_756,plain,
% 3.18/1.00      ( k1_lattices(sK4,k2_lattices(sK4,X0_46,X1_46),X1_46) = X1_46
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1263,plain,
% 3.18/1.00      ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,X0_46,X1_46),X2_46),X2_46) = X2_46
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X2_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_758,c_756]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2866,plain,
% 3.18/1.00      ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,sK5,X0_46),X1_46),X1_46) = X1_46
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top
% 3.18/1.00      | m1_subset_1(X1_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_1263]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3112,plain,
% 3.18/1.00      ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),X0_46),X0_46) = X0_46
% 3.18/1.00      | m1_subset_1(X0_46,u1_struct_0(sK4)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_2866]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3133,plain,
% 3.18/1.00      ( k1_lattices(sK4,k2_lattices(sK4,k1_lattices(sK4,sK5,sK5),sK5),sK5) = sK5 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_753,c_3112]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5418,plain,
% 3.18/1.00      ( k1_lattices(sK4,sK5,sK5) = sK5 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_5240,c_3133]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_13,negated_conjecture,
% 3.18/1.00      ( k1_lattices(sK4,sK5,sK5) != sK5 ),
% 3.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_634,negated_conjecture,
% 3.18/1.00      ( k1_lattices(sK4,sK5,sK5) != sK5 ),
% 3.18/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,[status(thm)],[c_5418,c_634]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.01
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.011
% 3.18/1.00  total_time:                             0.217
% 3.18/1.00  num_of_symbols:                         49
% 3.18/1.00  num_of_terms:                           4363
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    21
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        3
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        1
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       52
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        20
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        1
% 3.18/1.00  pred_elim:                              7
% 3.18/1.00  pred_elim_cl:                           13
% 3.18/1.00  pred_elim_cycles:                       11
% 3.18/1.00  merged_defs:                            0
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          0
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.006
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                7
% 3.18/1.00  conjectures:                            2
% 3.18/1.00  epr:                                    0
% 3.18/1.00  horn:                                   7
% 3.18/1.00  ground:                                 2
% 3.18/1.00  unary:                                  2
% 3.18/1.00  binary:                                 0
% 3.18/1.00  lits:                                   17
% 3.18/1.00  lits_eq:                                5
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                0
% 3.18/1.00  fd_pseudo_cond:                         0
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      29
% 3.18/1.00  prop_fast_solver_calls:                 501
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    1354
% 3.18/1.00  prop_preprocess_simplified:             4012
% 3.18/1.00  prop_fo_subsumed:                       13
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    694
% 3.18/1.00  inst_num_in_passive:                    210
% 3.18/1.00  inst_num_in_active:                     262
% 3.18/1.00  inst_num_in_unprocessed:                222
% 3.18/1.00  inst_num_of_loops:                      290
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          22
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      774
% 3.18/1.00  inst_num_of_non_proper_insts:           1068
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       56
% 3.18/1.00  res_forward_subset_subsumed:            86
% 3.18/1.00  res_backward_subset_subsumed:           0
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       565
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      143
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     82
% 3.18/1.00  sup_num_in_active:                      52
% 3.18/1.00  sup_num_in_passive:                     30
% 3.18/1.00  sup_num_of_loops:                       56
% 3.18/1.00  sup_fw_superposition:                   73
% 3.18/1.00  sup_bw_superposition:                   11
% 3.18/1.00  sup_immediate_simplified:               9
% 3.18/1.00  sup_given_eliminated:                   0
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    0
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 1
% 3.18/1.00  sim_bw_subset_subsumed:                 0
% 3.18/1.00  sim_fw_subsumed:                        0
% 3.18/1.00  sim_bw_subsumed:                        0
% 3.18/1.00  sim_fw_subsumption_res:                 0
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      3
% 3.18/1.00  sim_eq_tautology_del:                   5
% 3.18/1.00  sim_eq_res_simp:                        0
% 3.18/1.00  sim_fw_demodulated:                     0
% 3.18/1.00  sim_bw_demodulated:                     4
% 3.18/1.00  sim_light_normalised:                   8
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1192+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:07 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
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

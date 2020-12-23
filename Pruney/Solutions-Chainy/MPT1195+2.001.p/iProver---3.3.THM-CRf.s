%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:11 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 512 expanded)
%              Number of clauses        :   65 ( 128 expanded)
%              Number of leaves         :   15 ( 147 expanded)
%              Depth                    :   18
%              Number of atoms          :  482 (3811 expanded)
%              Number of equality atoms :  163 ( 911 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
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
    inference(ennf_transformation,[],[f1])).

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

fof(f17,plain,(
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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X1,X2) != X1
            | ~ r1_lattices(X0,X1,X2) )
          & ( k2_lattices(X0,X1,X2) = X1
            | r1_lattices(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,X1,sK6) != X1
          | ~ r1_lattices(X0,X1,sK6) )
        & ( k2_lattices(X0,X1,sK6) = X1
          | r1_lattices(X0,X1,sK6) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( k2_lattices(X0,sK5,X2) != sK5
              | ~ r1_lattices(X0,sK5,X2) )
            & ( k2_lattices(X0,sK5,X2) = sK5
              | r1_lattices(X0,sK5,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_lattices(X0,X1,X2) != X1
                  | ~ r1_lattices(X0,X1,X2) )
                & ( k2_lattices(X0,X1,X2) = X1
                  | r1_lattices(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(sK4,X1,X2) != X1
                | ~ r1_lattices(sK4,X1,X2) )
              & ( k2_lattices(sK4,X1,X2) = X1
                | r1_lattices(sK4,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v9_lattices(sK4)
      & v8_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k2_lattices(sK4,sK5,sK6) != sK5
      | ~ r1_lattices(sK4,sK5,sK6) )
    & ( k2_lattices(sK4,sK5,sK6) = sK5
      | r1_lattices(sK4,sK5,sK6) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v9_lattices(sK4)
    & v8_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f51,plain,
    ( k2_lattices(sK4,sK5,sK6) = sK5
    | r1_lattices(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f10,plain,(
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
    inference(flattening,[],[f10])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    v8_lattices(sK4) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK3(X0))) != X1
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).

fof(f40,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    v9_lattices(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,
    ( k2_lattices(sK4,sK5,sK6) != sK5
    | ~ r1_lattices(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_238,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_10,c_1])).

cnf(c_12,negated_conjecture,
    ( r1_lattices(sK4,sK5,sK6)
    | k2_lattices(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_129,plain,
    ( r1_lattices(sK4,sK5,sK6)
    | k2_lattices(sK4,sK5,sK6) = sK5 ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(sK4,sK5,sK6) = sK5
    | k1_lattices(X1,X2,X0) = X0
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_238,c_129])).

cnf(c_312,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | k2_lattices(sK4,sK5,sK6) = sK5
    | k1_lattices(sK4,sK5,sK6) = sK6 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_314,plain,
    ( k2_lattices(sK4,sK5,sK6) = sK5
    | k1_lattices(sK4,sK5,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_18,c_15,c_14,c_13])).

cnf(c_402,plain,
    ( k1_lattices(sK4,sK5,sK6) = sK6
    | k2_lattices(sK4,sK5,sK6) = sK5 ),
    inference(prop_impl,[status(thm)],[c_314])).

cnf(c_403,plain,
    ( k2_lattices(sK4,sK5,sK6) = sK5
    | k1_lattices(sK4,sK5,sK6) = sK6 ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_437,plain,
    ( k2_lattices(sK4,sK5,sK6) = sK5
    | k1_lattices(sK4,sK5,sK6) = sK6 ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_442,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_451,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_635,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_443,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_632,plain,
    ( X0_45 != X1_45
    | sK6 != X1_45
    | sK6 = X0_45 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_634,plain,
    ( X0_45 != sK6
    | sK6 = X0_45
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_667,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6) != sK6
    | sK6 = k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_669,plain,
    ( k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6) != sK6
    | sK6 = k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | ~ v8_lattices(sK4)
    | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_17,negated_conjecture,
    ( v8_lattices(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_17,c_15])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK4))
    | k1_lattices(sK4,k2_lattices(sK4,X0_45,X1_45),X1_45) = X1_45 ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_671,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_615,plain,
    ( k1_lattices(sK4,sK5,sK6) != X0_45
    | k1_lattices(sK4,sK5,sK6) = sK6
    | sK6 != X0_45 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_683,plain,
    ( k1_lattices(sK4,sK5,sK6) != k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6)
    | k1_lattices(sK4,sK5,sK6) = sK6
    | sK6 != k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_684,plain,
    ( k1_lattices(sK4,sK5,sK6) != k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6)
    | k1_lattices(sK4,sK5,sK6) = sK6
    | sK6 != k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_444,plain,
    ( X0_45 != X1_45
    | X2_45 != X3_45
    | k1_lattices(X0_47,X0_45,X2_45) = k1_lattices(X0_47,X1_45,X3_45) ),
    theory(equality)).

cnf(c_695,plain,
    ( k1_lattices(sK4,sK5,sK6) = k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6)
    | sK6 != sK6
    | sK5 != k2_lattices(sK4,X0_45,sK6) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_696,plain,
    ( k1_lattices(sK4,sK5,sK6) = k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6)
    | sK6 != sK6
    | sK5 != k2_lattices(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_852,plain,
    ( k2_lattices(sK4,X0_45,sK6) != X1_45
    | sK5 != X1_45
    | sK5 = k2_lattices(sK4,X0_45,sK6) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_853,plain,
    ( k2_lattices(sK4,sK5,sK6) != sK5
    | sK5 = k2_lattices(sK4,sK5,sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_854,plain,
    ( k1_lattices(sK4,sK5,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_14,c_13,c_451,c_635,c_669,c_671,c_684,c_696,c_853])).

cnf(c_440,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_578,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_439,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_579,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v9_lattices(sK4)
    | ~ l3_lattices(sK4)
    | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_16,negated_conjecture,
    ( v9_lattices(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_16,c_15])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK4))
    | k2_lattices(sK4,X0_45,k1_lattices(sK4,X0_45,X1_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_580,plain,
    ( k2_lattices(sK4,X0_45,k1_lattices(sK4,X0_45,X1_45)) = X0_45
    | m1_subset_1(X0_45,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_645,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_45)) = sK5
    | m1_subset_1(X0_45,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_580])).

cnf(c_805,plain,
    ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK6)) = sK5 ),
    inference(superposition,[status(thm)],[c_578,c_645])).

cnf(c_857,plain,
    ( k2_lattices(sK4,sK5,sK6) = sK5 ),
    inference(demodulation,[status(thm)],[c_854,c_805])).

cnf(c_0,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_261,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_10,c_0])).

cnf(c_11,negated_conjecture,
    ( ~ r1_lattices(sK4,sK5,sK6)
    | k2_lattices(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_127,plain,
    ( ~ r1_lattices(sK4,sK5,sK6)
    | k2_lattices(sK4,sK5,sK6) != sK5 ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(sK4,sK5,sK6) != sK5
    | k1_lattices(X1,X2,X0) != X0
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_127])).

cnf(c_301,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | k2_lattices(sK4,sK5,sK6) != sK5
    | k1_lattices(sK4,sK5,sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_303,plain,
    ( k2_lattices(sK4,sK5,sK6) != sK5
    | k1_lattices(sK4,sK5,sK6) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_18,c_15,c_14,c_13])).

cnf(c_400,plain,
    ( k1_lattices(sK4,sK5,sK6) != sK6
    | k2_lattices(sK4,sK5,sK6) != sK5 ),
    inference(prop_impl,[status(thm)],[c_303])).

cnf(c_401,plain,
    ( k2_lattices(sK4,sK5,sK6) != sK5
    | k1_lattices(sK4,sK5,sK6) != sK6 ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_438,plain,
    ( k2_lattices(sK4,sK5,sK6) != sK5
    | k1_lattices(sK4,sK5,sK6) != sK6 ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_857,c_854,c_438])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.22/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.22/1.02  
% 1.22/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.22/1.02  
% 1.22/1.02  ------  iProver source info
% 1.22/1.02  
% 1.22/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.22/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.22/1.02  git: non_committed_changes: false
% 1.22/1.02  git: last_make_outside_of_git: false
% 1.22/1.02  
% 1.22/1.02  ------ 
% 1.22/1.02  
% 1.22/1.02  ------ Input Options
% 1.22/1.02  
% 1.22/1.02  --out_options                           all
% 1.22/1.02  --tptp_safe_out                         true
% 1.22/1.02  --problem_path                          ""
% 1.22/1.02  --include_path                          ""
% 1.22/1.02  --clausifier                            res/vclausify_rel
% 1.22/1.02  --clausifier_options                    --mode clausify
% 1.22/1.02  --stdin                                 false
% 1.22/1.02  --stats_out                             all
% 1.22/1.02  
% 1.22/1.02  ------ General Options
% 1.22/1.02  
% 1.22/1.02  --fof                                   false
% 1.22/1.02  --time_out_real                         305.
% 1.22/1.02  --time_out_virtual                      -1.
% 1.22/1.02  --symbol_type_check                     false
% 1.22/1.02  --clausify_out                          false
% 1.22/1.02  --sig_cnt_out                           false
% 1.22/1.02  --trig_cnt_out                          false
% 1.22/1.02  --trig_cnt_out_tolerance                1.
% 1.22/1.02  --trig_cnt_out_sk_spl                   false
% 1.22/1.02  --abstr_cl_out                          false
% 1.22/1.02  
% 1.22/1.02  ------ Global Options
% 1.22/1.02  
% 1.22/1.02  --schedule                              default
% 1.22/1.02  --add_important_lit                     false
% 1.22/1.02  --prop_solver_per_cl                    1000
% 1.22/1.02  --min_unsat_core                        false
% 1.22/1.02  --soft_assumptions                      false
% 1.22/1.02  --soft_lemma_size                       3
% 1.22/1.02  --prop_impl_unit_size                   0
% 1.22/1.02  --prop_impl_unit                        []
% 1.22/1.02  --share_sel_clauses                     true
% 1.22/1.02  --reset_solvers                         false
% 1.22/1.02  --bc_imp_inh                            [conj_cone]
% 1.22/1.02  --conj_cone_tolerance                   3.
% 1.22/1.02  --extra_neg_conj                        none
% 1.22/1.02  --large_theory_mode                     true
% 1.22/1.02  --prolific_symb_bound                   200
% 1.22/1.02  --lt_threshold                          2000
% 1.22/1.02  --clause_weak_htbl                      true
% 1.22/1.02  --gc_record_bc_elim                     false
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing Options
% 1.22/1.02  
% 1.22/1.02  --preprocessing_flag                    true
% 1.22/1.02  --time_out_prep_mult                    0.1
% 1.22/1.02  --splitting_mode                        input
% 1.22/1.02  --splitting_grd                         true
% 1.22/1.02  --splitting_cvd                         false
% 1.22/1.02  --splitting_cvd_svl                     false
% 1.22/1.02  --splitting_nvd                         32
% 1.22/1.02  --sub_typing                            true
% 1.22/1.02  --prep_gs_sim                           true
% 1.22/1.02  --prep_unflatten                        true
% 1.22/1.02  --prep_res_sim                          true
% 1.22/1.02  --prep_upred                            true
% 1.22/1.02  --prep_sem_filter                       exhaustive
% 1.22/1.02  --prep_sem_filter_out                   false
% 1.22/1.02  --pred_elim                             true
% 1.22/1.02  --res_sim_input                         true
% 1.22/1.02  --eq_ax_congr_red                       true
% 1.22/1.02  --pure_diseq_elim                       true
% 1.22/1.02  --brand_transform                       false
% 1.22/1.02  --non_eq_to_eq                          false
% 1.22/1.02  --prep_def_merge                        true
% 1.22/1.02  --prep_def_merge_prop_impl              false
% 1.22/1.02  --prep_def_merge_mbd                    true
% 1.22/1.02  --prep_def_merge_tr_red                 false
% 1.22/1.02  --prep_def_merge_tr_cl                  false
% 1.22/1.02  --smt_preprocessing                     true
% 1.22/1.02  --smt_ac_axioms                         fast
% 1.22/1.02  --preprocessed_out                      false
% 1.22/1.02  --preprocessed_stats                    false
% 1.22/1.02  
% 1.22/1.02  ------ Abstraction refinement Options
% 1.22/1.02  
% 1.22/1.02  --abstr_ref                             []
% 1.22/1.02  --abstr_ref_prep                        false
% 1.22/1.02  --abstr_ref_until_sat                   false
% 1.22/1.02  --abstr_ref_sig_restrict                funpre
% 1.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.22/1.02  --abstr_ref_under                       []
% 1.22/1.02  
% 1.22/1.02  ------ SAT Options
% 1.22/1.02  
% 1.22/1.02  --sat_mode                              false
% 1.22/1.02  --sat_fm_restart_options                ""
% 1.22/1.02  --sat_gr_def                            false
% 1.22/1.02  --sat_epr_types                         true
% 1.22/1.02  --sat_non_cyclic_types                  false
% 1.22/1.02  --sat_finite_models                     false
% 1.22/1.02  --sat_fm_lemmas                         false
% 1.22/1.02  --sat_fm_prep                           false
% 1.22/1.02  --sat_fm_uc_incr                        true
% 1.22/1.02  --sat_out_model                         small
% 1.22/1.02  --sat_out_clauses                       false
% 1.22/1.02  
% 1.22/1.02  ------ QBF Options
% 1.22/1.02  
% 1.22/1.02  --qbf_mode                              false
% 1.22/1.02  --qbf_elim_univ                         false
% 1.22/1.02  --qbf_dom_inst                          none
% 1.22/1.02  --qbf_dom_pre_inst                      false
% 1.22/1.02  --qbf_sk_in                             false
% 1.22/1.02  --qbf_pred_elim                         true
% 1.22/1.02  --qbf_split                             512
% 1.22/1.02  
% 1.22/1.02  ------ BMC1 Options
% 1.22/1.02  
% 1.22/1.02  --bmc1_incremental                      false
% 1.22/1.02  --bmc1_axioms                           reachable_all
% 1.22/1.02  --bmc1_min_bound                        0
% 1.22/1.02  --bmc1_max_bound                        -1
% 1.22/1.02  --bmc1_max_bound_default                -1
% 1.22/1.02  --bmc1_symbol_reachability              true
% 1.22/1.02  --bmc1_property_lemmas                  false
% 1.22/1.02  --bmc1_k_induction                      false
% 1.22/1.02  --bmc1_non_equiv_states                 false
% 1.22/1.02  --bmc1_deadlock                         false
% 1.22/1.02  --bmc1_ucm                              false
% 1.22/1.02  --bmc1_add_unsat_core                   none
% 1.22/1.02  --bmc1_unsat_core_children              false
% 1.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.22/1.02  --bmc1_out_stat                         full
% 1.22/1.02  --bmc1_ground_init                      false
% 1.22/1.02  --bmc1_pre_inst_next_state              false
% 1.22/1.02  --bmc1_pre_inst_state                   false
% 1.22/1.02  --bmc1_pre_inst_reach_state             false
% 1.22/1.02  --bmc1_out_unsat_core                   false
% 1.22/1.02  --bmc1_aig_witness_out                  false
% 1.22/1.02  --bmc1_verbose                          false
% 1.22/1.02  --bmc1_dump_clauses_tptp                false
% 1.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.22/1.02  --bmc1_dump_file                        -
% 1.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.22/1.02  --bmc1_ucm_extend_mode                  1
% 1.22/1.02  --bmc1_ucm_init_mode                    2
% 1.22/1.02  --bmc1_ucm_cone_mode                    none
% 1.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.22/1.02  --bmc1_ucm_relax_model                  4
% 1.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.22/1.02  --bmc1_ucm_layered_model                none
% 1.22/1.02  --bmc1_ucm_max_lemma_size               10
% 1.22/1.02  
% 1.22/1.02  ------ AIG Options
% 1.22/1.02  
% 1.22/1.02  --aig_mode                              false
% 1.22/1.02  
% 1.22/1.02  ------ Instantiation Options
% 1.22/1.02  
% 1.22/1.02  --instantiation_flag                    true
% 1.22/1.02  --inst_sos_flag                         false
% 1.22/1.02  --inst_sos_phase                        true
% 1.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel_side                     num_symb
% 1.22/1.02  --inst_solver_per_active                1400
% 1.22/1.02  --inst_solver_calls_frac                1.
% 1.22/1.02  --inst_passive_queue_type               priority_queues
% 1.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.22/1.02  --inst_passive_queues_freq              [25;2]
% 1.22/1.02  --inst_dismatching                      true
% 1.22/1.02  --inst_eager_unprocessed_to_passive     true
% 1.22/1.02  --inst_prop_sim_given                   true
% 1.22/1.02  --inst_prop_sim_new                     false
% 1.22/1.02  --inst_subs_new                         false
% 1.22/1.02  --inst_eq_res_simp                      false
% 1.22/1.02  --inst_subs_given                       false
% 1.22/1.02  --inst_orphan_elimination               true
% 1.22/1.02  --inst_learning_loop_flag               true
% 1.22/1.02  --inst_learning_start                   3000
% 1.22/1.02  --inst_learning_factor                  2
% 1.22/1.02  --inst_start_prop_sim_after_learn       3
% 1.22/1.02  --inst_sel_renew                        solver
% 1.22/1.02  --inst_lit_activity_flag                true
% 1.22/1.02  --inst_restr_to_given                   false
% 1.22/1.02  --inst_activity_threshold               500
% 1.22/1.02  --inst_out_proof                        true
% 1.22/1.02  
% 1.22/1.02  ------ Resolution Options
% 1.22/1.02  
% 1.22/1.02  --resolution_flag                       true
% 1.22/1.02  --res_lit_sel                           adaptive
% 1.22/1.02  --res_lit_sel_side                      none
% 1.22/1.02  --res_ordering                          kbo
% 1.22/1.02  --res_to_prop_solver                    active
% 1.22/1.02  --res_prop_simpl_new                    false
% 1.22/1.02  --res_prop_simpl_given                  true
% 1.22/1.02  --res_passive_queue_type                priority_queues
% 1.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.22/1.02  --res_passive_queues_freq               [15;5]
% 1.22/1.02  --res_forward_subs                      full
% 1.22/1.02  --res_backward_subs                     full
% 1.22/1.02  --res_forward_subs_resolution           true
% 1.22/1.02  --res_backward_subs_resolution          true
% 1.22/1.02  --res_orphan_elimination                true
% 1.22/1.02  --res_time_limit                        2.
% 1.22/1.02  --res_out_proof                         true
% 1.22/1.02  
% 1.22/1.02  ------ Superposition Options
% 1.22/1.02  
% 1.22/1.02  --superposition_flag                    true
% 1.22/1.02  --sup_passive_queue_type                priority_queues
% 1.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.22/1.02  --demod_completeness_check              fast
% 1.22/1.02  --demod_use_ground                      true
% 1.22/1.02  --sup_to_prop_solver                    passive
% 1.22/1.02  --sup_prop_simpl_new                    true
% 1.22/1.02  --sup_prop_simpl_given                  true
% 1.22/1.02  --sup_fun_splitting                     false
% 1.22/1.02  --sup_smt_interval                      50000
% 1.22/1.02  
% 1.22/1.02  ------ Superposition Simplification Setup
% 1.22/1.02  
% 1.22/1.02  --sup_indices_passive                   []
% 1.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_full_bw                           [BwDemod]
% 1.22/1.02  --sup_immed_triv                        [TrivRules]
% 1.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_immed_bw_main                     []
% 1.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.02  
% 1.22/1.02  ------ Combination Options
% 1.22/1.02  
% 1.22/1.02  --comb_res_mult                         3
% 1.22/1.02  --comb_sup_mult                         2
% 1.22/1.02  --comb_inst_mult                        10
% 1.22/1.02  
% 1.22/1.02  ------ Debug Options
% 1.22/1.02  
% 1.22/1.02  --dbg_backtrace                         false
% 1.22/1.02  --dbg_dump_prop_clauses                 false
% 1.22/1.02  --dbg_dump_prop_clauses_file            -
% 1.22/1.02  --dbg_out_stat                          false
% 1.22/1.02  ------ Parsing...
% 1.22/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.22/1.02  ------ Proving...
% 1.22/1.02  ------ Problem Properties 
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  clauses                                 6
% 1.22/1.02  conjectures                             2
% 1.22/1.02  EPR                                     0
% 1.22/1.02  Horn                                    5
% 1.22/1.02  unary                                   2
% 1.22/1.02  binary                                  2
% 1.22/1.02  lits                                    12
% 1.22/1.02  lits eq                                 6
% 1.22/1.02  fd_pure                                 0
% 1.22/1.02  fd_pseudo                               0
% 1.22/1.02  fd_cond                                 0
% 1.22/1.02  fd_pseudo_cond                          0
% 1.22/1.02  AC symbols                              0
% 1.22/1.02  
% 1.22/1.02  ------ Schedule dynamic 5 is on 
% 1.22/1.02  
% 1.22/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  ------ 
% 1.22/1.02  Current options:
% 1.22/1.02  ------ 
% 1.22/1.02  
% 1.22/1.02  ------ Input Options
% 1.22/1.02  
% 1.22/1.02  --out_options                           all
% 1.22/1.02  --tptp_safe_out                         true
% 1.22/1.02  --problem_path                          ""
% 1.22/1.02  --include_path                          ""
% 1.22/1.02  --clausifier                            res/vclausify_rel
% 1.22/1.02  --clausifier_options                    --mode clausify
% 1.22/1.02  --stdin                                 false
% 1.22/1.02  --stats_out                             all
% 1.22/1.02  
% 1.22/1.02  ------ General Options
% 1.22/1.02  
% 1.22/1.02  --fof                                   false
% 1.22/1.02  --time_out_real                         305.
% 1.22/1.02  --time_out_virtual                      -1.
% 1.22/1.02  --symbol_type_check                     false
% 1.22/1.02  --clausify_out                          false
% 1.22/1.02  --sig_cnt_out                           false
% 1.22/1.02  --trig_cnt_out                          false
% 1.22/1.02  --trig_cnt_out_tolerance                1.
% 1.22/1.02  --trig_cnt_out_sk_spl                   false
% 1.22/1.02  --abstr_cl_out                          false
% 1.22/1.02  
% 1.22/1.02  ------ Global Options
% 1.22/1.02  
% 1.22/1.02  --schedule                              default
% 1.22/1.02  --add_important_lit                     false
% 1.22/1.02  --prop_solver_per_cl                    1000
% 1.22/1.02  --min_unsat_core                        false
% 1.22/1.02  --soft_assumptions                      false
% 1.22/1.02  --soft_lemma_size                       3
% 1.22/1.02  --prop_impl_unit_size                   0
% 1.22/1.02  --prop_impl_unit                        []
% 1.22/1.02  --share_sel_clauses                     true
% 1.22/1.02  --reset_solvers                         false
% 1.22/1.02  --bc_imp_inh                            [conj_cone]
% 1.22/1.02  --conj_cone_tolerance                   3.
% 1.22/1.02  --extra_neg_conj                        none
% 1.22/1.02  --large_theory_mode                     true
% 1.22/1.02  --prolific_symb_bound                   200
% 1.22/1.02  --lt_threshold                          2000
% 1.22/1.02  --clause_weak_htbl                      true
% 1.22/1.02  --gc_record_bc_elim                     false
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing Options
% 1.22/1.02  
% 1.22/1.02  --preprocessing_flag                    true
% 1.22/1.02  --time_out_prep_mult                    0.1
% 1.22/1.02  --splitting_mode                        input
% 1.22/1.02  --splitting_grd                         true
% 1.22/1.02  --splitting_cvd                         false
% 1.22/1.02  --splitting_cvd_svl                     false
% 1.22/1.02  --splitting_nvd                         32
% 1.22/1.02  --sub_typing                            true
% 1.22/1.02  --prep_gs_sim                           true
% 1.22/1.02  --prep_unflatten                        true
% 1.22/1.02  --prep_res_sim                          true
% 1.22/1.02  --prep_upred                            true
% 1.22/1.02  --prep_sem_filter                       exhaustive
% 1.22/1.02  --prep_sem_filter_out                   false
% 1.22/1.02  --pred_elim                             true
% 1.22/1.02  --res_sim_input                         true
% 1.22/1.02  --eq_ax_congr_red                       true
% 1.22/1.02  --pure_diseq_elim                       true
% 1.22/1.02  --brand_transform                       false
% 1.22/1.02  --non_eq_to_eq                          false
% 1.22/1.02  --prep_def_merge                        true
% 1.22/1.02  --prep_def_merge_prop_impl              false
% 1.22/1.02  --prep_def_merge_mbd                    true
% 1.22/1.02  --prep_def_merge_tr_red                 false
% 1.22/1.02  --prep_def_merge_tr_cl                  false
% 1.22/1.02  --smt_preprocessing                     true
% 1.22/1.02  --smt_ac_axioms                         fast
% 1.22/1.02  --preprocessed_out                      false
% 1.22/1.02  --preprocessed_stats                    false
% 1.22/1.02  
% 1.22/1.02  ------ Abstraction refinement Options
% 1.22/1.02  
% 1.22/1.02  --abstr_ref                             []
% 1.22/1.02  --abstr_ref_prep                        false
% 1.22/1.02  --abstr_ref_until_sat                   false
% 1.22/1.02  --abstr_ref_sig_restrict                funpre
% 1.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.22/1.02  --abstr_ref_under                       []
% 1.22/1.02  
% 1.22/1.02  ------ SAT Options
% 1.22/1.02  
% 1.22/1.02  --sat_mode                              false
% 1.22/1.02  --sat_fm_restart_options                ""
% 1.22/1.02  --sat_gr_def                            false
% 1.22/1.02  --sat_epr_types                         true
% 1.22/1.02  --sat_non_cyclic_types                  false
% 1.22/1.02  --sat_finite_models                     false
% 1.22/1.02  --sat_fm_lemmas                         false
% 1.22/1.02  --sat_fm_prep                           false
% 1.22/1.02  --sat_fm_uc_incr                        true
% 1.22/1.02  --sat_out_model                         small
% 1.22/1.02  --sat_out_clauses                       false
% 1.22/1.02  
% 1.22/1.02  ------ QBF Options
% 1.22/1.02  
% 1.22/1.02  --qbf_mode                              false
% 1.22/1.02  --qbf_elim_univ                         false
% 1.22/1.02  --qbf_dom_inst                          none
% 1.22/1.02  --qbf_dom_pre_inst                      false
% 1.22/1.02  --qbf_sk_in                             false
% 1.22/1.02  --qbf_pred_elim                         true
% 1.22/1.02  --qbf_split                             512
% 1.22/1.02  
% 1.22/1.02  ------ BMC1 Options
% 1.22/1.02  
% 1.22/1.02  --bmc1_incremental                      false
% 1.22/1.02  --bmc1_axioms                           reachable_all
% 1.22/1.02  --bmc1_min_bound                        0
% 1.22/1.02  --bmc1_max_bound                        -1
% 1.22/1.02  --bmc1_max_bound_default                -1
% 1.22/1.02  --bmc1_symbol_reachability              true
% 1.22/1.02  --bmc1_property_lemmas                  false
% 1.22/1.02  --bmc1_k_induction                      false
% 1.22/1.02  --bmc1_non_equiv_states                 false
% 1.22/1.02  --bmc1_deadlock                         false
% 1.22/1.02  --bmc1_ucm                              false
% 1.22/1.02  --bmc1_add_unsat_core                   none
% 1.22/1.02  --bmc1_unsat_core_children              false
% 1.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.22/1.02  --bmc1_out_stat                         full
% 1.22/1.02  --bmc1_ground_init                      false
% 1.22/1.02  --bmc1_pre_inst_next_state              false
% 1.22/1.02  --bmc1_pre_inst_state                   false
% 1.22/1.02  --bmc1_pre_inst_reach_state             false
% 1.22/1.02  --bmc1_out_unsat_core                   false
% 1.22/1.02  --bmc1_aig_witness_out                  false
% 1.22/1.02  --bmc1_verbose                          false
% 1.22/1.02  --bmc1_dump_clauses_tptp                false
% 1.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.22/1.02  --bmc1_dump_file                        -
% 1.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.22/1.02  --bmc1_ucm_extend_mode                  1
% 1.22/1.02  --bmc1_ucm_init_mode                    2
% 1.22/1.02  --bmc1_ucm_cone_mode                    none
% 1.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.22/1.02  --bmc1_ucm_relax_model                  4
% 1.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.22/1.02  --bmc1_ucm_layered_model                none
% 1.22/1.02  --bmc1_ucm_max_lemma_size               10
% 1.22/1.02  
% 1.22/1.02  ------ AIG Options
% 1.22/1.02  
% 1.22/1.02  --aig_mode                              false
% 1.22/1.02  
% 1.22/1.02  ------ Instantiation Options
% 1.22/1.02  
% 1.22/1.02  --instantiation_flag                    true
% 1.22/1.02  --inst_sos_flag                         false
% 1.22/1.02  --inst_sos_phase                        true
% 1.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel_side                     none
% 1.22/1.02  --inst_solver_per_active                1400
% 1.22/1.02  --inst_solver_calls_frac                1.
% 1.22/1.02  --inst_passive_queue_type               priority_queues
% 1.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.22/1.02  --inst_passive_queues_freq              [25;2]
% 1.22/1.02  --inst_dismatching                      true
% 1.22/1.02  --inst_eager_unprocessed_to_passive     true
% 1.22/1.02  --inst_prop_sim_given                   true
% 1.22/1.02  --inst_prop_sim_new                     false
% 1.22/1.02  --inst_subs_new                         false
% 1.22/1.02  --inst_eq_res_simp                      false
% 1.22/1.02  --inst_subs_given                       false
% 1.22/1.02  --inst_orphan_elimination               true
% 1.22/1.02  --inst_learning_loop_flag               true
% 1.22/1.02  --inst_learning_start                   3000
% 1.22/1.02  --inst_learning_factor                  2
% 1.22/1.02  --inst_start_prop_sim_after_learn       3
% 1.22/1.02  --inst_sel_renew                        solver
% 1.22/1.02  --inst_lit_activity_flag                true
% 1.22/1.02  --inst_restr_to_given                   false
% 1.22/1.02  --inst_activity_threshold               500
% 1.22/1.02  --inst_out_proof                        true
% 1.22/1.02  
% 1.22/1.02  ------ Resolution Options
% 1.22/1.02  
% 1.22/1.02  --resolution_flag                       false
% 1.22/1.02  --res_lit_sel                           adaptive
% 1.22/1.02  --res_lit_sel_side                      none
% 1.22/1.02  --res_ordering                          kbo
% 1.22/1.02  --res_to_prop_solver                    active
% 1.22/1.02  --res_prop_simpl_new                    false
% 1.22/1.02  --res_prop_simpl_given                  true
% 1.22/1.02  --res_passive_queue_type                priority_queues
% 1.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.22/1.02  --res_passive_queues_freq               [15;5]
% 1.22/1.02  --res_forward_subs                      full
% 1.22/1.02  --res_backward_subs                     full
% 1.22/1.02  --res_forward_subs_resolution           true
% 1.22/1.02  --res_backward_subs_resolution          true
% 1.22/1.02  --res_orphan_elimination                true
% 1.22/1.02  --res_time_limit                        2.
% 1.22/1.02  --res_out_proof                         true
% 1.22/1.02  
% 1.22/1.02  ------ Superposition Options
% 1.22/1.02  
% 1.22/1.02  --superposition_flag                    true
% 1.22/1.02  --sup_passive_queue_type                priority_queues
% 1.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.22/1.02  --demod_completeness_check              fast
% 1.22/1.02  --demod_use_ground                      true
% 1.22/1.02  --sup_to_prop_solver                    passive
% 1.22/1.02  --sup_prop_simpl_new                    true
% 1.22/1.02  --sup_prop_simpl_given                  true
% 1.22/1.02  --sup_fun_splitting                     false
% 1.22/1.02  --sup_smt_interval                      50000
% 1.22/1.02  
% 1.22/1.02  ------ Superposition Simplification Setup
% 1.22/1.02  
% 1.22/1.02  --sup_indices_passive                   []
% 1.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_full_bw                           [BwDemod]
% 1.22/1.02  --sup_immed_triv                        [TrivRules]
% 1.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_immed_bw_main                     []
% 1.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.02  
% 1.22/1.02  ------ Combination Options
% 1.22/1.02  
% 1.22/1.02  --comb_res_mult                         3
% 1.22/1.02  --comb_sup_mult                         2
% 1.22/1.02  --comb_inst_mult                        10
% 1.22/1.02  
% 1.22/1.02  ------ Debug Options
% 1.22/1.02  
% 1.22/1.02  --dbg_backtrace                         false
% 1.22/1.02  --dbg_dump_prop_clauses                 false
% 1.22/1.02  --dbg_dump_prop_clauses_file            -
% 1.22/1.02  --dbg_out_stat                          false
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  ------ Proving...
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  % SZS status Theorem for theBenchmark.p
% 1.22/1.02  
% 1.22/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.22/1.02  
% 1.22/1.02  fof(f4,axiom,(
% 1.22/1.02    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.02  
% 1.22/1.02  fof(f7,plain,(
% 1.22/1.02    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.22/1.02    inference(pure_predicate_removal,[],[f4])).
% 1.22/1.02  
% 1.22/1.02  fof(f14,plain,(
% 1.22/1.02    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.22/1.02    inference(ennf_transformation,[],[f7])).
% 1.22/1.02  
% 1.22/1.02  fof(f44,plain,(
% 1.22/1.02    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.22/1.02    inference(cnf_transformation,[],[f14])).
% 1.22/1.02  
% 1.22/1.02  fof(f1,axiom,(
% 1.22/1.02    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.02  
% 1.22/1.02  fof(f8,plain,(
% 1.22/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.22/1.02    inference(ennf_transformation,[],[f1])).
% 1.22/1.02  
% 1.22/1.02  fof(f9,plain,(
% 1.22/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(flattening,[],[f8])).
% 1.22/1.02  
% 1.22/1.02  fof(f17,plain,(
% 1.22/1.02    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(nnf_transformation,[],[f9])).
% 1.22/1.02  
% 1.22/1.02  fof(f34,plain,(
% 1.22/1.02    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.22/1.02    inference(cnf_transformation,[],[f17])).
% 1.22/1.02  
% 1.22/1.02  fof(f5,conjecture,(
% 1.22/1.02    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.02  
% 1.22/1.02  fof(f6,negated_conjecture,(
% 1.22/1.02    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.22/1.02    inference(negated_conjecture,[],[f5])).
% 1.22/1.02  
% 1.22/1.02  fof(f15,plain,(
% 1.22/1.02    ? [X0] : (? [X1] : (? [X2] : ((r1_lattices(X0,X1,X2) <~> k2_lattices(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)))),
% 1.22/1.02    inference(ennf_transformation,[],[f6])).
% 1.22/1.02  
% 1.22/1.02  fof(f16,plain,(
% 1.22/1.02    ? [X0] : (? [X1] : (? [X2] : ((r1_lattices(X0,X1,X2) <~> k2_lattices(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0))),
% 1.22/1.02    inference(flattening,[],[f15])).
% 1.22/1.02  
% 1.22/1.02  fof(f28,plain,(
% 1.22/1.02    ? [X0] : (? [X1] : (? [X2] : (((k2_lattices(X0,X1,X2) != X1 | ~r1_lattices(X0,X1,X2)) & (k2_lattices(X0,X1,X2) = X1 | r1_lattices(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0))),
% 1.22/1.02    inference(nnf_transformation,[],[f16])).
% 1.22/1.02  
% 1.22/1.02  fof(f29,plain,(
% 1.22/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_lattices(X0,X1,X2) != X1 | ~r1_lattices(X0,X1,X2)) & (k2_lattices(X0,X1,X2) = X1 | r1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0))),
% 1.22/1.02    inference(flattening,[],[f28])).
% 1.22/1.02  
% 1.22/1.02  fof(f32,plain,(
% 1.22/1.02    ( ! [X0,X1] : (? [X2] : ((k2_lattices(X0,X1,X2) != X1 | ~r1_lattices(X0,X1,X2)) & (k2_lattices(X0,X1,X2) = X1 | r1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,X1,sK6) != X1 | ~r1_lattices(X0,X1,sK6)) & (k2_lattices(X0,X1,sK6) = X1 | r1_lattices(X0,X1,sK6)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f31,plain,(
% 1.22/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((k2_lattices(X0,X1,X2) != X1 | ~r1_lattices(X0,X1,X2)) & (k2_lattices(X0,X1,X2) = X1 | r1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((k2_lattices(X0,sK5,X2) != sK5 | ~r1_lattices(X0,sK5,X2)) & (k2_lattices(X0,sK5,X2) = sK5 | r1_lattices(X0,sK5,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f30,plain,(
% 1.22/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_lattices(X0,X1,X2) != X1 | ~r1_lattices(X0,X1,X2)) & (k2_lattices(X0,X1,X2) = X1 | r1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_lattices(sK4,X1,X2) != X1 | ~r1_lattices(sK4,X1,X2)) & (k2_lattices(sK4,X1,X2) = X1 | r1_lattices(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v9_lattices(sK4) & v8_lattices(sK4) & ~v2_struct_0(sK4))),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f33,plain,(
% 1.22/1.02    (((k2_lattices(sK4,sK5,sK6) != sK5 | ~r1_lattices(sK4,sK5,sK6)) & (k2_lattices(sK4,sK5,sK6) = sK5 | r1_lattices(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v9_lattices(sK4) & v8_lattices(sK4) & ~v2_struct_0(sK4)),
% 1.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 1.22/1.02  
% 1.22/1.02  fof(f51,plain,(
% 1.22/1.02    k2_lattices(sK4,sK5,sK6) = sK5 | r1_lattices(sK4,sK5,sK6)),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f45,plain,(
% 1.22/1.02    ~v2_struct_0(sK4)),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f48,plain,(
% 1.22/1.02    l3_lattices(sK4)),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f49,plain,(
% 1.22/1.02    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f50,plain,(
% 1.22/1.02    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f2,axiom,(
% 1.22/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.02  
% 1.22/1.02  fof(f10,plain,(
% 1.22/1.02    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.22/1.02    inference(ennf_transformation,[],[f2])).
% 1.22/1.02  
% 1.22/1.02  fof(f11,plain,(
% 1.22/1.02    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(flattening,[],[f10])).
% 1.22/1.02  
% 1.22/1.02  fof(f18,plain,(
% 1.22/1.02    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(nnf_transformation,[],[f11])).
% 1.22/1.02  
% 1.22/1.02  fof(f19,plain,(
% 1.22/1.02    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(rectify,[],[f18])).
% 1.22/1.02  
% 1.22/1.02  fof(f21,plain,(
% 1.22/1.02    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f20,plain,(
% 1.22/1.02    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f22,plain,(
% 1.22/1.02    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 1.22/1.02  
% 1.22/1.02  fof(f36,plain,(
% 1.22/1.02    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.22/1.02    inference(cnf_transformation,[],[f22])).
% 1.22/1.02  
% 1.22/1.02  fof(f46,plain,(
% 1.22/1.02    v8_lattices(sK4)),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f3,axiom,(
% 1.22/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 1.22/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.22/1.02  
% 1.22/1.02  fof(f12,plain,(
% 1.22/1.02    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.22/1.02    inference(ennf_transformation,[],[f3])).
% 1.22/1.02  
% 1.22/1.02  fof(f13,plain,(
% 1.22/1.02    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(flattening,[],[f12])).
% 1.22/1.02  
% 1.22/1.02  fof(f23,plain,(
% 1.22/1.02    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(nnf_transformation,[],[f13])).
% 1.22/1.02  
% 1.22/1.02  fof(f24,plain,(
% 1.22/1.02    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(rectify,[],[f23])).
% 1.22/1.02  
% 1.22/1.02  fof(f26,plain,(
% 1.22/1.02    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK3(X0))) != X1 & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f25,plain,(
% 1.22/1.02    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) != sK2(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 1.22/1.02    introduced(choice_axiom,[])).
% 1.22/1.02  
% 1.22/1.02  fof(f27,plain,(
% 1.22/1.02    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != sK2(X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).
% 1.22/1.02  
% 1.22/1.02  fof(f40,plain,(
% 1.22/1.02    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.22/1.02    inference(cnf_transformation,[],[f27])).
% 1.22/1.02  
% 1.22/1.02  fof(f47,plain,(
% 1.22/1.02    v9_lattices(sK4)),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  fof(f35,plain,(
% 1.22/1.02    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.22/1.02    inference(cnf_transformation,[],[f17])).
% 1.22/1.02  
% 1.22/1.02  fof(f52,plain,(
% 1.22/1.02    k2_lattices(sK4,sK5,sK6) != sK5 | ~r1_lattices(sK4,sK5,sK6)),
% 1.22/1.02    inference(cnf_transformation,[],[f33])).
% 1.22/1.02  
% 1.22/1.02  cnf(c_10,plain,
% 1.22/1.02      ( ~ l3_lattices(X0) | l2_lattices(X0) ),
% 1.22/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_1,plain,
% 1.22/1.02      ( ~ r1_lattices(X0,X1,X2)
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.22/1.02      | v2_struct_0(X0)
% 1.22/1.02      | ~ l2_lattices(X0)
% 1.22/1.02      | k1_lattices(X0,X1,X2) = X2 ),
% 1.22/1.02      inference(cnf_transformation,[],[f34]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_238,plain,
% 1.22/1.02      ( ~ r1_lattices(X0,X1,X2)
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.22/1.02      | ~ l3_lattices(X0)
% 1.22/1.02      | v2_struct_0(X0)
% 1.22/1.02      | k1_lattices(X0,X1,X2) = X2 ),
% 1.22/1.02      inference(resolution,[status(thm)],[c_10,c_1]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_12,negated_conjecture,
% 1.22/1.02      ( r1_lattices(sK4,sK5,sK6) | k2_lattices(sK4,sK5,sK6) = sK5 ),
% 1.22/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_129,plain,
% 1.22/1.02      ( r1_lattices(sK4,sK5,sK6) | k2_lattices(sK4,sK5,sK6) = sK5 ),
% 1.22/1.02      inference(prop_impl,[status(thm)],[c_12]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_311,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.22/1.02      | ~ l3_lattices(X1)
% 1.22/1.02      | v2_struct_0(X1)
% 1.22/1.02      | k2_lattices(sK4,sK5,sK6) = sK5
% 1.22/1.02      | k1_lattices(X1,X2,X0) = X0
% 1.22/1.02      | sK6 != X0
% 1.22/1.02      | sK5 != X2
% 1.22/1.02      | sK4 != X1 ),
% 1.22/1.02      inference(resolution_lifted,[status(thm)],[c_238,c_129]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_312,plain,
% 1.22/1.02      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.22/1.02      | ~ l3_lattices(sK4)
% 1.22/1.02      | v2_struct_0(sK4)
% 1.22/1.02      | k2_lattices(sK4,sK5,sK6) = sK5
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) = sK6 ),
% 1.22/1.02      inference(unflattening,[status(thm)],[c_311]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_18,negated_conjecture,
% 1.22/1.02      ( ~ v2_struct_0(sK4) ),
% 1.22/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_15,negated_conjecture,
% 1.22/1.02      ( l3_lattices(sK4) ),
% 1.22/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_14,negated_conjecture,
% 1.22/1.02      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.22/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_13,negated_conjecture,
% 1.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.22/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_314,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) = sK5 | k1_lattices(sK4,sK5,sK6) = sK6 ),
% 1.22/1.02      inference(global_propositional_subsumption,
% 1.22/1.02                [status(thm)],
% 1.22/1.02                [c_312,c_18,c_15,c_14,c_13]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_402,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) = sK6 | k2_lattices(sK4,sK5,sK6) = sK5 ),
% 1.22/1.02      inference(prop_impl,[status(thm)],[c_314]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_403,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) = sK5 | k1_lattices(sK4,sK5,sK6) = sK6 ),
% 1.22/1.02      inference(renaming,[status(thm)],[c_402]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_437,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) = sK5 | k1_lattices(sK4,sK5,sK6) = sK6 ),
% 1.22/1.02      inference(subtyping,[status(esa)],[c_403]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_442,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_451,plain,
% 1.22/1.02      ( sK5 = sK5 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_442]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_635,plain,
% 1.22/1.02      ( sK6 = sK6 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_442]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_443,plain,
% 1.22/1.02      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.22/1.02      theory(equality) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_632,plain,
% 1.22/1.02      ( X0_45 != X1_45 | sK6 != X1_45 | sK6 = X0_45 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_443]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_634,plain,
% 1.22/1.02      ( X0_45 != sK6 | sK6 = X0_45 | sK6 != sK6 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_632]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_667,plain,
% 1.22/1.02      ( k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6) != sK6
% 1.22/1.02      | sK6 = k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6)
% 1.22/1.02      | sK6 != sK6 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_634]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_669,plain,
% 1.22/1.02      ( k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6) != sK6
% 1.22/1.02      | sK6 = k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6)
% 1.22/1.02      | sK6 != sK6 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_667]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_5,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.22/1.02      | ~ l3_lattices(X1)
% 1.22/1.02      | ~ v8_lattices(X1)
% 1.22/1.02      | v2_struct_0(X1)
% 1.22/1.02      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 1.22/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_359,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.22/1.02      | ~ l3_lattices(X1)
% 1.22/1.02      | ~ v8_lattices(X1)
% 1.22/1.02      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 1.22/1.02      | sK4 != X1 ),
% 1.22/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_360,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.22/1.02      | ~ l3_lattices(sK4)
% 1.22/1.02      | ~ v8_lattices(sK4)
% 1.22/1.02      | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
% 1.22/1.02      inference(unflattening,[status(thm)],[c_359]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_17,negated_conjecture,
% 1.22/1.02      ( v8_lattices(sK4) ),
% 1.22/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_364,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.22/1.02      | k1_lattices(sK4,k2_lattices(sK4,X0,X1),X1) = X1 ),
% 1.22/1.02      inference(global_propositional_subsumption,
% 1.22/1.02                [status(thm)],
% 1.22/1.02                [c_360,c_17,c_15]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_435,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0_45,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(X1_45,u1_struct_0(sK4))
% 1.22/1.02      | k1_lattices(sK4,k2_lattices(sK4,X0_45,X1_45),X1_45) = X1_45 ),
% 1.22/1.02      inference(subtyping,[status(esa)],[c_364]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_668,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0_45,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.22/1.02      | k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6) = sK6 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_435]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_671,plain,
% 1.22/1.02      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.22/1.02      | k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6) = sK6 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_668]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_615,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) != X0_45
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) = sK6
% 1.22/1.02      | sK6 != X0_45 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_443]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_683,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) != k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6)
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) = sK6
% 1.22/1.02      | sK6 != k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6) ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_615]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_684,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) != k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6)
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) = sK6
% 1.22/1.02      | sK6 != k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6) ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_683]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_444,plain,
% 1.22/1.02      ( X0_45 != X1_45
% 1.22/1.02      | X2_45 != X3_45
% 1.22/1.02      | k1_lattices(X0_47,X0_45,X2_45) = k1_lattices(X0_47,X1_45,X3_45) ),
% 1.22/1.02      theory(equality) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_695,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) = k1_lattices(sK4,k2_lattices(sK4,X0_45,sK6),sK6)
% 1.22/1.02      | sK6 != sK6
% 1.22/1.02      | sK5 != k2_lattices(sK4,X0_45,sK6) ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_444]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_696,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) = k1_lattices(sK4,k2_lattices(sK4,sK5,sK6),sK6)
% 1.22/1.02      | sK6 != sK6
% 1.22/1.02      | sK5 != k2_lattices(sK4,sK5,sK6) ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_695]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_852,plain,
% 1.22/1.02      ( k2_lattices(sK4,X0_45,sK6) != X1_45
% 1.22/1.02      | sK5 != X1_45
% 1.22/1.02      | sK5 = k2_lattices(sK4,X0_45,sK6) ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_443]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_853,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) != sK5
% 1.22/1.02      | sK5 = k2_lattices(sK4,sK5,sK6)
% 1.22/1.02      | sK5 != sK5 ),
% 1.22/1.02      inference(instantiation,[status(thm)],[c_852]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_854,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) = sK6 ),
% 1.22/1.02      inference(global_propositional_subsumption,
% 1.22/1.02                [status(thm)],
% 1.22/1.02                [c_437,c_14,c_13,c_451,c_635,c_669,c_671,c_684,c_696,
% 1.22/1.02                 c_853]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_440,negated_conjecture,
% 1.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.22/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_578,plain,
% 1.22/1.02      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 1.22/1.02      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_439,negated_conjecture,
% 1.22/1.02      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.22/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_579,plain,
% 1.22/1.02      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.22/1.02      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_9,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.22/1.02      | ~ v9_lattices(X1)
% 1.22/1.02      | ~ l3_lattices(X1)
% 1.22/1.02      | v2_struct_0(X1)
% 1.22/1.02      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 1.22/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_338,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.22/1.02      | ~ v9_lattices(X1)
% 1.22/1.02      | ~ l3_lattices(X1)
% 1.22/1.02      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 1.22/1.02      | sK4 != X1 ),
% 1.22/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_339,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.22/1.02      | ~ v9_lattices(sK4)
% 1.22/1.02      | ~ l3_lattices(sK4)
% 1.22/1.02      | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
% 1.22/1.02      inference(unflattening,[status(thm)],[c_338]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_16,negated_conjecture,
% 1.22/1.02      ( v9_lattices(sK4) ),
% 1.22/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_343,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.22/1.02      | k2_lattices(sK4,X0,k1_lattices(sK4,X0,X1)) = X0 ),
% 1.22/1.02      inference(global_propositional_subsumption,
% 1.22/1.02                [status(thm)],
% 1.22/1.02                [c_339,c_16,c_15]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_436,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0_45,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(X1_45,u1_struct_0(sK4))
% 1.22/1.02      | k2_lattices(sK4,X0_45,k1_lattices(sK4,X0_45,X1_45)) = X0_45 ),
% 1.22/1.02      inference(subtyping,[status(esa)],[c_343]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_580,plain,
% 1.22/1.02      ( k2_lattices(sK4,X0_45,k1_lattices(sK4,X0_45,X1_45)) = X0_45
% 1.22/1.02      | m1_subset_1(X0_45,u1_struct_0(sK4)) != iProver_top
% 1.22/1.02      | m1_subset_1(X1_45,u1_struct_0(sK4)) != iProver_top ),
% 1.22/1.02      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_645,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,X0_45)) = sK5
% 1.22/1.02      | m1_subset_1(X0_45,u1_struct_0(sK4)) != iProver_top ),
% 1.22/1.02      inference(superposition,[status(thm)],[c_579,c_580]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_805,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,k1_lattices(sK4,sK5,sK6)) = sK5 ),
% 1.22/1.02      inference(superposition,[status(thm)],[c_578,c_645]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_857,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) = sK5 ),
% 1.22/1.02      inference(demodulation,[status(thm)],[c_854,c_805]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_0,plain,
% 1.22/1.02      ( r1_lattices(X0,X1,X2)
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.22/1.02      | v2_struct_0(X0)
% 1.22/1.02      | ~ l2_lattices(X0)
% 1.22/1.02      | k1_lattices(X0,X1,X2) != X2 ),
% 1.22/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_261,plain,
% 1.22/1.02      ( r1_lattices(X0,X1,X2)
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.22/1.02      | ~ l3_lattices(X0)
% 1.22/1.02      | v2_struct_0(X0)
% 1.22/1.02      | k1_lattices(X0,X1,X2) != X2 ),
% 1.22/1.02      inference(resolution,[status(thm)],[c_10,c_0]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_11,negated_conjecture,
% 1.22/1.02      ( ~ r1_lattices(sK4,sK5,sK6) | k2_lattices(sK4,sK5,sK6) != sK5 ),
% 1.22/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_127,plain,
% 1.22/1.02      ( ~ r1_lattices(sK4,sK5,sK6) | k2_lattices(sK4,sK5,sK6) != sK5 ),
% 1.22/1.02      inference(prop_impl,[status(thm)],[c_11]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_300,plain,
% 1.22/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.22/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.22/1.02      | ~ l3_lattices(X1)
% 1.22/1.02      | v2_struct_0(X1)
% 1.22/1.02      | k2_lattices(sK4,sK5,sK6) != sK5
% 1.22/1.02      | k1_lattices(X1,X2,X0) != X0
% 1.22/1.02      | sK6 != X0
% 1.22/1.02      | sK5 != X2
% 1.22/1.02      | sK4 != X1 ),
% 1.22/1.02      inference(resolution_lifted,[status(thm)],[c_261,c_127]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_301,plain,
% 1.22/1.02      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.22/1.02      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.22/1.02      | ~ l3_lattices(sK4)
% 1.22/1.02      | v2_struct_0(sK4)
% 1.22/1.02      | k2_lattices(sK4,sK5,sK6) != sK5
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) != sK6 ),
% 1.22/1.02      inference(unflattening,[status(thm)],[c_300]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_303,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) != sK5
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) != sK6 ),
% 1.22/1.02      inference(global_propositional_subsumption,
% 1.22/1.02                [status(thm)],
% 1.22/1.02                [c_301,c_18,c_15,c_14,c_13]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_400,plain,
% 1.22/1.02      ( k1_lattices(sK4,sK5,sK6) != sK6
% 1.22/1.02      | k2_lattices(sK4,sK5,sK6) != sK5 ),
% 1.22/1.02      inference(prop_impl,[status(thm)],[c_303]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_401,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) != sK5
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) != sK6 ),
% 1.22/1.02      inference(renaming,[status(thm)],[c_400]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(c_438,plain,
% 1.22/1.02      ( k2_lattices(sK4,sK5,sK6) != sK5
% 1.22/1.02      | k1_lattices(sK4,sK5,sK6) != sK6 ),
% 1.22/1.02      inference(subtyping,[status(esa)],[c_401]) ).
% 1.22/1.02  
% 1.22/1.02  cnf(contradiction,plain,
% 1.22/1.02      ( $false ),
% 1.22/1.02      inference(minisat,[status(thm)],[c_857,c_854,c_438]) ).
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.22/1.02  
% 1.22/1.02  ------                               Statistics
% 1.22/1.02  
% 1.22/1.02  ------ General
% 1.22/1.02  
% 1.22/1.02  abstr_ref_over_cycles:                  0
% 1.22/1.02  abstr_ref_under_cycles:                 0
% 1.22/1.02  gc_basic_clause_elim:                   0
% 1.22/1.02  forced_gc_time:                         0
% 1.22/1.02  parsing_time:                           0.012
% 1.22/1.02  unif_index_cands_time:                  0.
% 1.22/1.02  unif_index_add_time:                    0.
% 1.22/1.02  orderings_time:                         0.
% 1.22/1.02  out_proof_time:                         0.012
% 1.22/1.02  total_time:                             0.108
% 1.22/1.02  num_of_symbols:                         48
% 1.22/1.02  num_of_terms:                           789
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing
% 1.22/1.02  
% 1.22/1.02  num_of_splits:                          0
% 1.22/1.02  num_of_split_atoms:                     0
% 1.22/1.02  num_of_reused_defs:                     0
% 1.22/1.02  num_eq_ax_congr_red:                    10
% 1.22/1.02  num_of_sem_filtered_clauses:            1
% 1.22/1.02  num_of_subtypes:                        3
% 1.22/1.02  monotx_restored_types:                  0
% 1.22/1.02  sat_num_of_epr_types:                   0
% 1.22/1.02  sat_num_of_non_cyclic_types:            0
% 1.22/1.02  sat_guarded_non_collapsed_types:        1
% 1.22/1.02  num_pure_diseq_elim:                    0
% 1.22/1.02  simp_replaced_by:                       0
% 1.22/1.02  res_preprocessed:                       48
% 1.22/1.02  prep_upred:                             0
% 1.22/1.02  prep_unflattend:                        14
% 1.22/1.02  smt_new_axioms:                         0
% 1.22/1.02  pred_elim_cands:                        1
% 1.22/1.02  pred_elim:                              6
% 1.22/1.02  pred_elim_cl:                           13
% 1.22/1.02  pred_elim_cycles:                       8
% 1.22/1.02  merged_defs:                            8
% 1.22/1.02  merged_defs_ncl:                        0
% 1.22/1.02  bin_hyper_res:                          8
% 1.22/1.02  prep_cycles:                            4
% 1.22/1.02  pred_elim_time:                         0.004
% 1.22/1.02  splitting_time:                         0.
% 1.22/1.02  sem_filter_time:                        0.
% 1.22/1.02  monotx_time:                            0.
% 1.22/1.02  subtype_inf_time:                       0.
% 1.22/1.02  
% 1.22/1.02  ------ Problem properties
% 1.22/1.02  
% 1.22/1.02  clauses:                                6
% 1.22/1.02  conjectures:                            2
% 1.22/1.02  epr:                                    0
% 1.22/1.02  horn:                                   5
% 1.22/1.02  ground:                                 4
% 1.22/1.02  unary:                                  2
% 1.22/1.02  binary:                                 2
% 1.22/1.02  lits:                                   12
% 1.22/1.02  lits_eq:                                6
% 1.22/1.02  fd_pure:                                0
% 1.22/1.02  fd_pseudo:                              0
% 1.22/1.02  fd_cond:                                0
% 1.22/1.02  fd_pseudo_cond:                         0
% 1.22/1.02  ac_symbols:                             0
% 1.22/1.02  
% 1.22/1.02  ------ Propositional Solver
% 1.22/1.02  
% 1.22/1.02  prop_solver_calls:                      26
% 1.22/1.02  prop_fast_solver_calls:                 305
% 1.22/1.02  smt_solver_calls:                       0
% 1.22/1.02  smt_fast_solver_calls:                  0
% 1.22/1.02  prop_num_of_clauses:                    229
% 1.22/1.02  prop_preprocess_simplified:             1187
% 1.22/1.02  prop_fo_subsumed:                       13
% 1.22/1.02  prop_solver_time:                       0.
% 1.22/1.02  smt_solver_time:                        0.
% 1.22/1.02  smt_fast_solver_time:                   0.
% 1.22/1.02  prop_fast_solver_time:                  0.
% 1.22/1.02  prop_unsat_core_time:                   0.
% 1.22/1.02  
% 1.22/1.02  ------ QBF
% 1.22/1.02  
% 1.22/1.02  qbf_q_res:                              0
% 1.22/1.02  qbf_num_tautologies:                    0
% 1.22/1.02  qbf_prep_cycles:                        0
% 1.22/1.02  
% 1.22/1.02  ------ BMC1
% 1.22/1.02  
% 1.22/1.02  bmc1_current_bound:                     -1
% 1.22/1.02  bmc1_last_solved_bound:                 -1
% 1.22/1.02  bmc1_unsat_core_size:                   -1
% 1.22/1.02  bmc1_unsat_core_parents_size:           -1
% 1.22/1.02  bmc1_merge_next_fun:                    0
% 1.22/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.22/1.02  
% 1.22/1.02  ------ Instantiation
% 1.22/1.02  
% 1.22/1.02  inst_num_of_clauses:                    64
% 1.22/1.02  inst_num_in_passive:                    11
% 1.22/1.02  inst_num_in_active:                     41
% 1.22/1.02  inst_num_in_unprocessed:                12
% 1.22/1.02  inst_num_of_loops:                      50
% 1.22/1.02  inst_num_of_learning_restarts:          0
% 1.22/1.02  inst_num_moves_active_passive:          4
% 1.22/1.02  inst_lit_activity:                      0
% 1.22/1.02  inst_lit_activity_moves:                0
% 1.22/1.02  inst_num_tautologies:                   0
% 1.22/1.02  inst_num_prop_implied:                  0
% 1.22/1.02  inst_num_existing_simplified:           0
% 1.22/1.02  inst_num_eq_res_simplified:             0
% 1.22/1.02  inst_num_child_elim:                    0
% 1.22/1.02  inst_num_of_dismatching_blockings:      10
% 1.22/1.02  inst_num_of_non_proper_insts:           55
% 1.22/1.02  inst_num_of_duplicates:                 0
% 1.22/1.02  inst_inst_num_from_inst_to_res:         0
% 1.22/1.02  inst_dismatching_checking_time:         0.
% 1.22/1.02  
% 1.22/1.02  ------ Resolution
% 1.22/1.02  
% 1.22/1.02  res_num_of_clauses:                     0
% 1.22/1.02  res_num_in_passive:                     0
% 1.22/1.02  res_num_in_active:                      0
% 1.22/1.02  res_num_of_loops:                       52
% 1.22/1.02  res_forward_subset_subsumed:            12
% 1.22/1.02  res_backward_subset_subsumed:           0
% 1.22/1.02  res_forward_subsumed:                   0
% 1.22/1.02  res_backward_subsumed:                  0
% 1.22/1.02  res_forward_subsumption_resolution:     0
% 1.22/1.02  res_backward_subsumption_resolution:    0
% 1.22/1.02  res_clause_to_clause_subsumption:       14
% 1.22/1.02  res_orphan_elimination:                 0
% 1.22/1.02  res_tautology_del:                      24
% 1.22/1.02  res_num_eq_res_simplified:              0
% 1.22/1.02  res_num_sel_changes:                    0
% 1.22/1.02  res_moves_from_active_to_pass:          0
% 1.22/1.02  
% 1.22/1.02  ------ Superposition
% 1.22/1.02  
% 1.22/1.02  sup_time_total:                         0.
% 1.22/1.02  sup_time_generating:                    0.
% 1.22/1.02  sup_time_sim_full:                      0.
% 1.22/1.02  sup_time_sim_immed:                     0.
% 1.22/1.02  
% 1.22/1.02  sup_num_of_clauses:                     12
% 1.22/1.02  sup_num_in_active:                      7
% 1.22/1.02  sup_num_in_passive:                     5
% 1.22/1.02  sup_num_of_loops:                       8
% 1.22/1.02  sup_fw_superposition:                   6
% 1.22/1.02  sup_bw_superposition:                   0
% 1.22/1.02  sup_immediate_simplified:               0
% 1.22/1.02  sup_given_eliminated:                   0
% 1.22/1.02  comparisons_done:                       0
% 1.22/1.02  comparisons_avoided:                    0
% 1.22/1.02  
% 1.22/1.02  ------ Simplifications
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  sim_fw_subset_subsumed:                 0
% 1.22/1.02  sim_bw_subset_subsumed:                 0
% 1.22/1.02  sim_fw_subsumed:                        0
% 1.22/1.02  sim_bw_subsumed:                        0
% 1.22/1.02  sim_fw_subsumption_res:                 0
% 1.22/1.02  sim_bw_subsumption_res:                 0
% 1.22/1.02  sim_tautology_del:                      0
% 1.22/1.02  sim_eq_tautology_del:                   0
% 1.22/1.02  sim_eq_res_simp:                        0
% 1.22/1.02  sim_fw_demodulated:                     0
% 1.22/1.02  sim_bw_demodulated:                     1
% 1.22/1.02  sim_light_normalised:                   0
% 1.22/1.02  sim_joinable_taut:                      0
% 1.22/1.02  sim_joinable_simp:                      0
% 1.22/1.02  sim_ac_normalised:                      0
% 1.22/1.02  sim_smt_subsumption:                    0
% 1.22/1.02  
%------------------------------------------------------------------------------

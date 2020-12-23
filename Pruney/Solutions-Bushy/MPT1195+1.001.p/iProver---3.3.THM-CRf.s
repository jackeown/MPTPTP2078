%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1195+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.23s
% Output     : CNFRefutation 1.23s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

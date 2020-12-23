%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1198+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:08 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 290 expanded)
%              Number of clauses        :   42 (  55 expanded)
%              Number of leaves         :   10 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  340 (2288 expanded)
%              Number of equality atoms :   69 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_lattices(X0,X2,X3)
                        & r1_lattices(X0,X1,X2) )
                     => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r1_lattices(X0,X2,X3)
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK6)
        & r1_lattices(X0,X2,sK6)
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X1,X3)
              & r1_lattices(X0,X2,X3)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r1_lattices(X0,sK5,X3)
            & r1_lattices(X0,X1,sK5)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(X0,sK4,X3)
                & r1_lattices(X0,X2,X3)
                & r1_lattices(X0,sK4,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r1_lattices(X0,X2,X3)
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK3,X1,X3)
                  & r1_lattices(sK3,X2,X3)
                  & r1_lattices(sK3,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l2_lattices(sK3)
      & v5_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_lattices(sK3,sK4,sK6)
    & r1_lattices(sK3,sK5,sK6)
    & r1_lattices(sK3,sK4,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l2_lattices(sK3)
    & v5_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f10,f21,f20,f19,f18])).

fof(f35,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f7,plain,(
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) != k1_lattices(X0,k1_lattices(X0,X1,X2),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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

fof(f14,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f25,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    l2_lattices(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    v5_lattices(sK3) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f5,plain,(
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

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    r1_lattices(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    r1_lattices(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ~ r1_lattices(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_291,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_372,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_290,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_373,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_289,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_374,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,k1_lattices(X1,X3,X2),X0) = k1_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_13,negated_conjecture,
    ( l2_lattices(sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X3,k1_lattices(X1,X2,X0)) = k1_lattices(X1,k1_lattices(X1,X3,X2),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v5_lattices(sK3)
    | v2_struct_0(sK3)
    | k1_lattices(sK3,X0,k1_lattices(sK3,X1,X2)) = k1_lattices(sK3,k1_lattices(sK3,X0,X1),X2) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( v5_lattices(sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k1_lattices(sK3,X0,k1_lattices(sK3,X1,X2)) = k1_lattices(sK3,k1_lattices(sK3,X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_15,c_14])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k1_lattices(sK3,X1,k1_lattices(sK3,X2,X0)) = k1_lattices(sK3,k1_lattices(sK3,X1,X2),X0) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_42,u1_struct_0(sK3))
    | k1_lattices(sK3,X1_42,k1_lattices(sK3,X2_42,X0_42)) = k1_lattices(sK3,k1_lattices(sK3,X1_42,X2_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_228])).

cnf(c_375,plain,
    ( k1_lattices(sK3,X0_42,k1_lattices(sK3,X1_42,X2_42)) = k1_lattices(sK3,k1_lattices(sK3,X0_42,X1_42),X2_42)
    | m1_subset_1(X2_42,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_42,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_547,plain,
    ( k1_lattices(sK3,k1_lattices(sK3,sK4,X0_42),X1_42) = k1_lattices(sK3,sK4,k1_lattices(sK3,X0_42,X1_42))
    | m1_subset_1(X0_42,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_42,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_374,c_375])).

cnf(c_1711,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK5,X0_42)) = k1_lattices(sK3,k1_lattices(sK3,sK4,sK5),X0_42)
    | m1_subset_1(X0_42,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_547])).

cnf(c_1,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,negated_conjecture,
    ( r1_lattices(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,X2,X0) = X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_178,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l2_lattices(sK3)
    | k1_lattices(sK3,sK4,sK5) = sK5 ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_180,plain,
    ( k1_lattices(sK3,sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_15,c_13,c_12,c_11])).

cnf(c_286,plain,
    ( k1_lattices(sK3,sK4,sK5) = sK5 ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_1719,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK5,X0_42)) = k1_lattices(sK3,sK5,X0_42)
    | m1_subset_1(X0_42,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1711,c_286])).

cnf(c_1973,plain,
    ( k1_lattices(sK3,sK4,k1_lattices(sK3,sK5,sK6)) = k1_lattices(sK3,sK5,sK6) ),
    inference(superposition,[status(thm)],[c_372,c_1719])).

cnf(c_8,negated_conjecture,
    ( r1_lattices(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,X2,X0) = X0
    | sK5 != X2
    | sK6 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_170,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l2_lattices(sK3)
    | k1_lattices(sK3,sK5,sK6) = sK6 ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_172,plain,
    ( k1_lattices(sK3,sK5,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_170,c_15,c_13,c_11,c_10])).

cnf(c_287,plain,
    ( k1_lattices(sK3,sK5,sK6) = sK6 ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_1981,plain,
    ( k1_lattices(sK3,sK4,sK6) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_1973,c_287])).

cnf(c_0,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,negated_conjecture,
    ( ~ r1_lattices(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_161,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | k1_lattices(X1,X2,X0) != X0
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_162,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l2_lattices(sK3)
    | k1_lattices(sK3,sK4,sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_164,plain,
    ( k1_lattices(sK3,sK4,sK6) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_162,c_15,c_13,c_12,c_10])).

cnf(c_288,plain,
    ( k1_lattices(sK3,sK4,sK6) != sK6 ),
    inference(subtyping,[status(esa)],[c_164])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1981,c_288])).


%------------------------------------------------------------------------------

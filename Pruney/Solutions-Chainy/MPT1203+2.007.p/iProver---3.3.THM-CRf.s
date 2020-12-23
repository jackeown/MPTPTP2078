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
% DateTime   : Thu Dec  3 12:13:15 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  205 (3709 expanded)
%              Number of clauses        :  138 ( 872 expanded)
%              Number of leaves         :   18 (1268 expanded)
%              Depth                    :   26
%              Number of atoms          :  806 (29125 expanded)
%              Number of equality atoms :  241 (9730 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                      & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                   => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                        & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                     => X2 = X3 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK8 != X2
        & k3_lattices(X0,X1,sK8) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK8) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK7 != X3
            & k3_lattices(X0,X1,sK7) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK7) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k3_lattices(X0,sK6,X2) = k3_lattices(X0,sK6,X3)
                & k4_lattices(X0,sK6,X2) = k4_lattices(X0,sK6,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                    & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(sK5,X1,X2) = k3_lattices(sK5,X1,X3)
                  & k4_lattices(sK5,X1,X2) = k4_lattices(sK5,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK5)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l3_lattices(sK5)
      & v11_lattices(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( sK7 != sK8
    & k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8)
    & k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l3_lattices(sK5)
    & v11_lattices(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f29,f44,f43,f42,f41])).

fof(f72,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f52,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v11_lattices(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
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
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f50,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
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

fof(f19,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f39,f38])).

fof(f57,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    sK7 != sK8 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_818,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_990,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_816,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_992,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_817,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_991,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_27,negated_conjecture,
    ( v11_lattices(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_27,c_26])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1,X2),k2_lattices(sK5,X1,X0)) = k2_lattices(sK5,X1,k1_lattices(sK5,X2,X0)) ),
    inference(renaming,[status(thm)],[c_718])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1_53,X2_53),k2_lattices(sK5,X1_53,X0_53)) = k2_lattices(sK5,X1_53,k1_lattices(sK5,X2_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_719])).

cnf(c_998,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_53,X1_53),k2_lattices(sK5,X0_53,X2_53)) = k2_lattices(sK5,X0_53,k1_lattices(sK5,X1_53,X2_53))
    | m1_subset_1(X2_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_2922,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,X0_53),k2_lattices(sK5,sK7,X1_53)) = k2_lattices(sK5,sK7,k1_lattices(sK5,X0_53,X1_53))
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_998])).

cnf(c_4066,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,X0_53)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_2922])).

cnf(c_16,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_444,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_445,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_79,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_447,plain,
    ( v6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_29,c_28,c_26,c_79])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_447])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X1,X0) = k4_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X1,X0) = k4_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_29,c_26])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | k2_lattices(sK5,X1_53,X0_53) = k4_lattices(sK5,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_542])).

cnf(c_996,plain,
    ( k2_lattices(sK5,X0_53,X1_53) = k4_lattices(sK5,X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_2260,plain,
    ( k2_lattices(sK5,sK7,X0_53) = k4_lattices(sK5,sK7,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_996])).

cnf(c_2426,plain,
    ( k2_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK7,sK6) ),
    inference(superposition,[status(thm)],[c_992,c_2260])).

cnf(c_4069,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,X0_53)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4066,c_2426])).

cnf(c_7512,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK8)) ),
    inference(superposition,[status(thm)],[c_990,c_4069])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_287])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_318])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k3_lattices(sK5,X0,X1) = k1_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k3_lattices(sK5,X0,X1) = k1_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_29,c_26])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | k3_lattices(sK5,X0_53,X1_53) = k1_lattices(sK5,X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_994,plain,
    ( k3_lattices(sK5,X0_53,X1_53) = k1_lattices(sK5,X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_1258,plain,
    ( k3_lattices(sK5,sK6,X0_53) = k1_lattices(sK5,sK6,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_994])).

cnf(c_1512,plain,
    ( k3_lattices(sK5,sK6,sK7) = k1_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_991,c_1258])).

cnf(c_1511,plain,
    ( k3_lattices(sK5,sK6,sK8) = k1_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_990,c_1258])).

cnf(c_21,negated_conjecture,
    ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_820,negated_conjecture,
    ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1539,plain,
    ( k3_lattices(sK5,sK6,sK7) = k1_lattices(sK5,sK6,sK8) ),
    inference(demodulation,[status(thm)],[c_1511,c_820])).

cnf(c_1592,plain,
    ( k1_lattices(sK5,sK6,sK7) = k1_lattices(sK5,sK6,sK8) ),
    inference(demodulation,[status(thm)],[c_1512,c_1539])).

cnf(c_2424,plain,
    ( k2_lattices(sK5,sK7,sK8) = k4_lattices(sK5,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_990,c_2260])).

cnf(c_2259,plain,
    ( k2_lattices(sK5,sK8,X0_53) = k4_lattices(sK5,sK8,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_996])).

cnf(c_2286,plain,
    ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK8,sK6) ),
    inference(superposition,[status(thm)],[c_992,c_2259])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_5])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_407,c_447])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k4_lattices(sK5,X1,X0) = k4_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_lattices(sK5,X1,X0) = k4_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_29,c_26])).

cnf(c_813,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | k4_lattices(sK5,X1_53,X0_53) = k4_lattices(sK5,X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_995,plain,
    ( k4_lattices(sK5,X0_53,X1_53) = k4_lattices(sK5,X1_53,X0_53)
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_1545,plain,
    ( k4_lattices(sK5,X0_53,sK7) = k4_lattices(sK5,sK7,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_995])).

cnf(c_1989,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_992,c_1545])).

cnf(c_1544,plain,
    ( k4_lattices(sK5,X0_53,sK8) = k4_lattices(sK5,sK8,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_995])).

cnf(c_1821,plain,
    ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_992,c_1544])).

cnf(c_22,negated_conjecture,
    ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_819,negated_conjecture,
    ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1893,plain,
    ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(demodulation,[status(thm)],[c_1821,c_819])).

cnf(c_1993,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK8,sK6) ),
    inference(demodulation,[status(thm)],[c_1989,c_1893])).

cnf(c_2288,plain,
    ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK7,sK6) ),
    inference(light_normalisation,[status(thm)],[c_2286,c_1993])).

cnf(c_2921,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,X0_53),k2_lattices(sK5,sK8,X1_53)) = k2_lattices(sK5,sK8,k1_lattices(sK5,X0_53,X1_53))
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_998])).

cnf(c_3401,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,X0_53)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_2921])).

cnf(c_3949,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,sK7)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_991,c_3401])).

cnf(c_5633,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK8,sK7)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) ),
    inference(demodulation,[status(thm)],[c_2288,c_3949])).

cnf(c_2285,plain,
    ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK8,sK7) ),
    inference(superposition,[status(thm)],[c_991,c_2259])).

cnf(c_1820,plain,
    ( k4_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_991,c_1544])).

cnf(c_2291,plain,
    ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK7,sK8) ),
    inference(light_normalisation,[status(thm)],[c_2285,c_1820])).

cnf(c_3948,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,sK8)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK8)) ),
    inference(superposition,[status(thm)],[c_990,c_3401])).

cnf(c_3956,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,sK8)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_3948,c_1592])).

cnf(c_2284,plain,
    ( k2_lattices(sK5,sK8,sK8) = k4_lattices(sK5,sK8,sK8) ),
    inference(superposition,[status(thm)],[c_990,c_2259])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k4_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | X1 != X2
    | k4_lattices(X1,X0,X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_349,c_1,c_2])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_367])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k4_lattices(sK5,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_29,c_26])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | k4_lattices(sK5,X0_53,X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_471])).

cnf(c_993,plain,
    ( k4_lattices(sK5,X0_53,X0_53) = X0_53
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_1162,plain,
    ( k4_lattices(sK5,sK8,sK8) = sK8 ),
    inference(superposition,[status(thm)],[c_990,c_993])).

cnf(c_2294,plain,
    ( k2_lattices(sK5,sK8,sK8) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_2284,c_1162])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_455,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_456,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_82,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_458,plain,
    ( v8_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_29,c_28,c_26,c_82])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_458])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_29,c_26,c_639])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1_53,X0_53),X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_699])).

cnf(c_997,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_53,X1_53),X1_53) = X1_53
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_2601,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_53),X0_53) = X0_53
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_997])).

cnf(c_3060,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),sK8) = sK8 ),
    inference(superposition,[status(thm)],[c_990,c_2601])).

cnf(c_2261,plain,
    ( k2_lattices(sK5,sK6,X0_53) = k4_lattices(sK5,sK6,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_996])).

cnf(c_2545,plain,
    ( k2_lattices(sK5,sK6,sK8) = k4_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_990,c_2261])).

cnf(c_3068,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,sK8),sK8) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_3060,c_2545])).

cnf(c_2175,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK8) ),
    inference(demodulation,[status(thm)],[c_1993,c_1821])).

cnf(c_5973,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),sK8) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_3068,c_2175])).

cnf(c_6539,plain,
    ( k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_3956,c_2288,c_2294,c_5973])).

cnf(c_6935,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k4_lattices(sK5,sK7,sK8)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_5633,c_2291,c_6539])).

cnf(c_7521,plain,
    ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK7)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_7512,c_1592,c_2424,c_6935])).

cnf(c_7513,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,sK7)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_991,c_4069])).

cnf(c_2425,plain,
    ( k2_lattices(sK5,sK7,sK7) = k4_lattices(sK5,sK7,sK7) ),
    inference(superposition,[status(thm)],[c_991,c_2260])).

cnf(c_1163,plain,
    ( k4_lattices(sK5,sK7,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_991,c_993])).

cnf(c_2430,plain,
    ( k2_lattices(sK5,sK7,sK7) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_2425,c_1163])).

cnf(c_2546,plain,
    ( k2_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_991,c_2261])).

cnf(c_2552,plain,
    ( k2_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK7,sK6) ),
    inference(light_normalisation,[status(thm)],[c_2546,c_1989])).

cnf(c_3061,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK7),sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_991,c_2601])).

cnf(c_5851,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),sK7) = sK7 ),
    inference(demodulation,[status(thm)],[c_2552,c_3061])).

cnf(c_7518,plain,
    ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK7)) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_7513,c_2430,c_5851])).

cnf(c_7636,plain,
    ( sK8 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_7521,c_7518])).

cnf(c_20,negated_conjecture,
    ( sK7 != sK8 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_821,negated_conjecture,
    ( sK7 != sK8 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_7673,plain,
    ( sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_7636,c_821])).

cnf(c_7674,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7673])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.42/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/0.99  
% 3.42/0.99  ------  iProver source info
% 3.42/0.99  
% 3.42/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.42/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/0.99  git: non_committed_changes: false
% 3.42/0.99  git: last_make_outside_of_git: false
% 3.42/0.99  
% 3.42/0.99  ------ 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options
% 3.42/0.99  
% 3.42/0.99  --out_options                           all
% 3.42/0.99  --tptp_safe_out                         true
% 3.42/0.99  --problem_path                          ""
% 3.42/0.99  --include_path                          ""
% 3.42/0.99  --clausifier                            res/vclausify_rel
% 3.42/0.99  --clausifier_options                    --mode clausify
% 3.42/0.99  --stdin                                 false
% 3.42/0.99  --stats_out                             all
% 3.42/0.99  
% 3.42/0.99  ------ General Options
% 3.42/0.99  
% 3.42/0.99  --fof                                   false
% 3.42/0.99  --time_out_real                         305.
% 3.42/0.99  --time_out_virtual                      -1.
% 3.42/0.99  --symbol_type_check                     false
% 3.42/0.99  --clausify_out                          false
% 3.42/0.99  --sig_cnt_out                           false
% 3.42/0.99  --trig_cnt_out                          false
% 3.42/0.99  --trig_cnt_out_tolerance                1.
% 3.42/0.99  --trig_cnt_out_sk_spl                   false
% 3.42/0.99  --abstr_cl_out                          false
% 3.42/0.99  
% 3.42/0.99  ------ Global Options
% 3.42/0.99  
% 3.42/0.99  --schedule                              default
% 3.42/0.99  --add_important_lit                     false
% 3.42/0.99  --prop_solver_per_cl                    1000
% 3.42/0.99  --min_unsat_core                        false
% 3.42/0.99  --soft_assumptions                      false
% 3.42/0.99  --soft_lemma_size                       3
% 3.42/0.99  --prop_impl_unit_size                   0
% 3.42/0.99  --prop_impl_unit                        []
% 3.42/0.99  --share_sel_clauses                     true
% 3.42/0.99  --reset_solvers                         false
% 3.42/0.99  --bc_imp_inh                            [conj_cone]
% 3.42/0.99  --conj_cone_tolerance                   3.
% 3.42/0.99  --extra_neg_conj                        none
% 3.42/0.99  --large_theory_mode                     true
% 3.42/0.99  --prolific_symb_bound                   200
% 3.42/0.99  --lt_threshold                          2000
% 3.42/0.99  --clause_weak_htbl                      true
% 3.42/0.99  --gc_record_bc_elim                     false
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing Options
% 3.42/0.99  
% 3.42/0.99  --preprocessing_flag                    true
% 3.42/0.99  --time_out_prep_mult                    0.1
% 3.42/0.99  --splitting_mode                        input
% 3.42/0.99  --splitting_grd                         true
% 3.42/0.99  --splitting_cvd                         false
% 3.42/0.99  --splitting_cvd_svl                     false
% 3.42/0.99  --splitting_nvd                         32
% 3.42/0.99  --sub_typing                            true
% 3.42/0.99  --prep_gs_sim                           true
% 3.42/0.99  --prep_unflatten                        true
% 3.42/0.99  --prep_res_sim                          true
% 3.42/0.99  --prep_upred                            true
% 3.42/0.99  --prep_sem_filter                       exhaustive
% 3.42/0.99  --prep_sem_filter_out                   false
% 3.42/0.99  --pred_elim                             true
% 3.42/0.99  --res_sim_input                         true
% 3.42/0.99  --eq_ax_congr_red                       true
% 3.42/0.99  --pure_diseq_elim                       true
% 3.42/0.99  --brand_transform                       false
% 3.42/0.99  --non_eq_to_eq                          false
% 3.42/0.99  --prep_def_merge                        true
% 3.42/0.99  --prep_def_merge_prop_impl              false
% 3.42/0.99  --prep_def_merge_mbd                    true
% 3.42/0.99  --prep_def_merge_tr_red                 false
% 3.42/0.99  --prep_def_merge_tr_cl                  false
% 3.42/0.99  --smt_preprocessing                     true
% 3.42/0.99  --smt_ac_axioms                         fast
% 3.42/0.99  --preprocessed_out                      false
% 3.42/0.99  --preprocessed_stats                    false
% 3.42/0.99  
% 3.42/0.99  ------ Abstraction refinement Options
% 3.42/0.99  
% 3.42/0.99  --abstr_ref                             []
% 3.42/0.99  --abstr_ref_prep                        false
% 3.42/0.99  --abstr_ref_until_sat                   false
% 3.42/0.99  --abstr_ref_sig_restrict                funpre
% 3.42/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.99  --abstr_ref_under                       []
% 3.42/0.99  
% 3.42/0.99  ------ SAT Options
% 3.42/0.99  
% 3.42/0.99  --sat_mode                              false
% 3.42/0.99  --sat_fm_restart_options                ""
% 3.42/0.99  --sat_gr_def                            false
% 3.42/0.99  --sat_epr_types                         true
% 3.42/0.99  --sat_non_cyclic_types                  false
% 3.42/0.99  --sat_finite_models                     false
% 3.42/0.99  --sat_fm_lemmas                         false
% 3.42/0.99  --sat_fm_prep                           false
% 3.42/0.99  --sat_fm_uc_incr                        true
% 3.42/0.99  --sat_out_model                         small
% 3.42/0.99  --sat_out_clauses                       false
% 3.42/0.99  
% 3.42/0.99  ------ QBF Options
% 3.42/0.99  
% 3.42/0.99  --qbf_mode                              false
% 3.42/0.99  --qbf_elim_univ                         false
% 3.42/0.99  --qbf_dom_inst                          none
% 3.42/0.99  --qbf_dom_pre_inst                      false
% 3.42/0.99  --qbf_sk_in                             false
% 3.42/0.99  --qbf_pred_elim                         true
% 3.42/0.99  --qbf_split                             512
% 3.42/0.99  
% 3.42/0.99  ------ BMC1 Options
% 3.42/0.99  
% 3.42/0.99  --bmc1_incremental                      false
% 3.42/0.99  --bmc1_axioms                           reachable_all
% 3.42/0.99  --bmc1_min_bound                        0
% 3.42/0.99  --bmc1_max_bound                        -1
% 3.42/0.99  --bmc1_max_bound_default                -1
% 3.42/0.99  --bmc1_symbol_reachability              true
% 3.42/0.99  --bmc1_property_lemmas                  false
% 3.42/0.99  --bmc1_k_induction                      false
% 3.42/0.99  --bmc1_non_equiv_states                 false
% 3.42/0.99  --bmc1_deadlock                         false
% 3.42/0.99  --bmc1_ucm                              false
% 3.42/0.99  --bmc1_add_unsat_core                   none
% 3.42/0.99  --bmc1_unsat_core_children              false
% 3.42/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.99  --bmc1_out_stat                         full
% 3.42/0.99  --bmc1_ground_init                      false
% 3.42/0.99  --bmc1_pre_inst_next_state              false
% 3.42/0.99  --bmc1_pre_inst_state                   false
% 3.42/0.99  --bmc1_pre_inst_reach_state             false
% 3.42/0.99  --bmc1_out_unsat_core                   false
% 3.42/0.99  --bmc1_aig_witness_out                  false
% 3.42/0.99  --bmc1_verbose                          false
% 3.42/0.99  --bmc1_dump_clauses_tptp                false
% 3.42/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.99  --bmc1_dump_file                        -
% 3.42/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.99  --bmc1_ucm_extend_mode                  1
% 3.42/0.99  --bmc1_ucm_init_mode                    2
% 3.42/0.99  --bmc1_ucm_cone_mode                    none
% 3.42/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.99  --bmc1_ucm_relax_model                  4
% 3.42/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.99  --bmc1_ucm_layered_model                none
% 3.42/0.99  --bmc1_ucm_max_lemma_size               10
% 3.42/0.99  
% 3.42/0.99  ------ AIG Options
% 3.42/0.99  
% 3.42/0.99  --aig_mode                              false
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation Options
% 3.42/0.99  
% 3.42/0.99  --instantiation_flag                    true
% 3.42/0.99  --inst_sos_flag                         false
% 3.42/0.99  --inst_sos_phase                        true
% 3.42/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel_side                     num_symb
% 3.42/0.99  --inst_solver_per_active                1400
% 3.42/0.99  --inst_solver_calls_frac                1.
% 3.42/0.99  --inst_passive_queue_type               priority_queues
% 3.42/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.99  --inst_passive_queues_freq              [25;2]
% 3.42/0.99  --inst_dismatching                      true
% 3.42/0.99  --inst_eager_unprocessed_to_passive     true
% 3.42/0.99  --inst_prop_sim_given                   true
% 3.42/0.99  --inst_prop_sim_new                     false
% 3.42/0.99  --inst_subs_new                         false
% 3.42/0.99  --inst_eq_res_simp                      false
% 3.42/0.99  --inst_subs_given                       false
% 3.42/0.99  --inst_orphan_elimination               true
% 3.42/0.99  --inst_learning_loop_flag               true
% 3.42/0.99  --inst_learning_start                   3000
% 3.42/0.99  --inst_learning_factor                  2
% 3.42/0.99  --inst_start_prop_sim_after_learn       3
% 3.42/0.99  --inst_sel_renew                        solver
% 3.42/0.99  --inst_lit_activity_flag                true
% 3.42/0.99  --inst_restr_to_given                   false
% 3.42/0.99  --inst_activity_threshold               500
% 3.42/0.99  --inst_out_proof                        true
% 3.42/0.99  
% 3.42/0.99  ------ Resolution Options
% 3.42/0.99  
% 3.42/0.99  --resolution_flag                       true
% 3.42/0.99  --res_lit_sel                           adaptive
% 3.42/0.99  --res_lit_sel_side                      none
% 3.42/0.99  --res_ordering                          kbo
% 3.42/0.99  --res_to_prop_solver                    active
% 3.42/0.99  --res_prop_simpl_new                    false
% 3.42/0.99  --res_prop_simpl_given                  true
% 3.42/0.99  --res_passive_queue_type                priority_queues
% 3.42/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.99  --res_passive_queues_freq               [15;5]
% 3.42/0.99  --res_forward_subs                      full
% 3.42/0.99  --res_backward_subs                     full
% 3.42/0.99  --res_forward_subs_resolution           true
% 3.42/0.99  --res_backward_subs_resolution          true
% 3.42/0.99  --res_orphan_elimination                true
% 3.42/0.99  --res_time_limit                        2.
% 3.42/0.99  --res_out_proof                         true
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Options
% 3.42/0.99  
% 3.42/0.99  --superposition_flag                    true
% 3.42/0.99  --sup_passive_queue_type                priority_queues
% 3.42/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.99  --demod_completeness_check              fast
% 3.42/0.99  --demod_use_ground                      true
% 3.42/0.99  --sup_to_prop_solver                    passive
% 3.42/0.99  --sup_prop_simpl_new                    true
% 3.42/0.99  --sup_prop_simpl_given                  true
% 3.42/0.99  --sup_fun_splitting                     false
% 3.42/0.99  --sup_smt_interval                      50000
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Simplification Setup
% 3.42/0.99  
% 3.42/0.99  --sup_indices_passive                   []
% 3.42/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_full_bw                           [BwDemod]
% 3.42/0.99  --sup_immed_triv                        [TrivRules]
% 3.42/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_immed_bw_main                     []
% 3.42/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  
% 3.42/0.99  ------ Combination Options
% 3.42/0.99  
% 3.42/0.99  --comb_res_mult                         3
% 3.42/0.99  --comb_sup_mult                         2
% 3.42/0.99  --comb_inst_mult                        10
% 3.42/0.99  
% 3.42/0.99  ------ Debug Options
% 3.42/0.99  
% 3.42/0.99  --dbg_backtrace                         false
% 3.42/0.99  --dbg_dump_prop_clauses                 false
% 3.42/0.99  --dbg_dump_prop_clauses_file            -
% 3.42/0.99  --dbg_out_stat                          false
% 3.42/0.99  ------ Parsing...
% 3.42/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/0.99  ------ Proving...
% 3.42/0.99  ------ Problem Properties 
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  clauses                                 12
% 3.42/0.99  conjectures                             6
% 3.42/0.99  EPR                                     1
% 3.42/0.99  Horn                                    12
% 3.42/0.99  unary                                   6
% 3.42/0.99  binary                                  1
% 3.42/0.99  lits                                    24
% 3.42/0.99  lits eq                                 9
% 3.42/0.99  fd_pure                                 0
% 3.42/0.99  fd_pseudo                               0
% 3.42/0.99  fd_cond                                 0
% 3.42/0.99  fd_pseudo_cond                          0
% 3.42/0.99  AC symbols                              0
% 3.42/0.99  
% 3.42/0.99  ------ Schedule dynamic 5 is on 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  ------ 
% 3.42/0.99  Current options:
% 3.42/0.99  ------ 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options
% 3.42/0.99  
% 3.42/0.99  --out_options                           all
% 3.42/0.99  --tptp_safe_out                         true
% 3.42/0.99  --problem_path                          ""
% 3.42/0.99  --include_path                          ""
% 3.42/0.99  --clausifier                            res/vclausify_rel
% 3.42/0.99  --clausifier_options                    --mode clausify
% 3.42/0.99  --stdin                                 false
% 3.42/0.99  --stats_out                             all
% 3.42/0.99  
% 3.42/0.99  ------ General Options
% 3.42/0.99  
% 3.42/0.99  --fof                                   false
% 3.42/0.99  --time_out_real                         305.
% 3.42/0.99  --time_out_virtual                      -1.
% 3.42/0.99  --symbol_type_check                     false
% 3.42/0.99  --clausify_out                          false
% 3.42/0.99  --sig_cnt_out                           false
% 3.42/0.99  --trig_cnt_out                          false
% 3.42/0.99  --trig_cnt_out_tolerance                1.
% 3.42/0.99  --trig_cnt_out_sk_spl                   false
% 3.42/0.99  --abstr_cl_out                          false
% 3.42/0.99  
% 3.42/0.99  ------ Global Options
% 3.42/0.99  
% 3.42/0.99  --schedule                              default
% 3.42/0.99  --add_important_lit                     false
% 3.42/0.99  --prop_solver_per_cl                    1000
% 3.42/0.99  --min_unsat_core                        false
% 3.42/0.99  --soft_assumptions                      false
% 3.42/0.99  --soft_lemma_size                       3
% 3.42/0.99  --prop_impl_unit_size                   0
% 3.42/0.99  --prop_impl_unit                        []
% 3.42/0.99  --share_sel_clauses                     true
% 3.42/0.99  --reset_solvers                         false
% 3.42/0.99  --bc_imp_inh                            [conj_cone]
% 3.42/0.99  --conj_cone_tolerance                   3.
% 3.42/0.99  --extra_neg_conj                        none
% 3.42/0.99  --large_theory_mode                     true
% 3.42/0.99  --prolific_symb_bound                   200
% 3.42/0.99  --lt_threshold                          2000
% 3.42/0.99  --clause_weak_htbl                      true
% 3.42/0.99  --gc_record_bc_elim                     false
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing Options
% 3.42/0.99  
% 3.42/0.99  --preprocessing_flag                    true
% 3.42/0.99  --time_out_prep_mult                    0.1
% 3.42/0.99  --splitting_mode                        input
% 3.42/0.99  --splitting_grd                         true
% 3.42/0.99  --splitting_cvd                         false
% 3.42/0.99  --splitting_cvd_svl                     false
% 3.42/0.99  --splitting_nvd                         32
% 3.42/0.99  --sub_typing                            true
% 3.42/0.99  --prep_gs_sim                           true
% 3.42/0.99  --prep_unflatten                        true
% 3.42/0.99  --prep_res_sim                          true
% 3.42/0.99  --prep_upred                            true
% 3.42/0.99  --prep_sem_filter                       exhaustive
% 3.42/0.99  --prep_sem_filter_out                   false
% 3.42/0.99  --pred_elim                             true
% 3.42/0.99  --res_sim_input                         true
% 3.42/0.99  --eq_ax_congr_red                       true
% 3.42/0.99  --pure_diseq_elim                       true
% 3.42/0.99  --brand_transform                       false
% 3.42/0.99  --non_eq_to_eq                          false
% 3.42/0.99  --prep_def_merge                        true
% 3.42/0.99  --prep_def_merge_prop_impl              false
% 3.42/0.99  --prep_def_merge_mbd                    true
% 3.42/0.99  --prep_def_merge_tr_red                 false
% 3.42/0.99  --prep_def_merge_tr_cl                  false
% 3.42/0.99  --smt_preprocessing                     true
% 3.42/0.99  --smt_ac_axioms                         fast
% 3.42/0.99  --preprocessed_out                      false
% 3.42/0.99  --preprocessed_stats                    false
% 3.42/0.99  
% 3.42/0.99  ------ Abstraction refinement Options
% 3.42/0.99  
% 3.42/0.99  --abstr_ref                             []
% 3.42/0.99  --abstr_ref_prep                        false
% 3.42/0.99  --abstr_ref_until_sat                   false
% 3.42/0.99  --abstr_ref_sig_restrict                funpre
% 3.42/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.99  --abstr_ref_under                       []
% 3.42/0.99  
% 3.42/0.99  ------ SAT Options
% 3.42/0.99  
% 3.42/0.99  --sat_mode                              false
% 3.42/0.99  --sat_fm_restart_options                ""
% 3.42/0.99  --sat_gr_def                            false
% 3.42/0.99  --sat_epr_types                         true
% 3.42/0.99  --sat_non_cyclic_types                  false
% 3.42/0.99  --sat_finite_models                     false
% 3.42/0.99  --sat_fm_lemmas                         false
% 3.42/0.99  --sat_fm_prep                           false
% 3.42/0.99  --sat_fm_uc_incr                        true
% 3.42/0.99  --sat_out_model                         small
% 3.42/0.99  --sat_out_clauses                       false
% 3.42/0.99  
% 3.42/0.99  ------ QBF Options
% 3.42/0.99  
% 3.42/0.99  --qbf_mode                              false
% 3.42/0.99  --qbf_elim_univ                         false
% 3.42/0.99  --qbf_dom_inst                          none
% 3.42/0.99  --qbf_dom_pre_inst                      false
% 3.42/0.99  --qbf_sk_in                             false
% 3.42/0.99  --qbf_pred_elim                         true
% 3.42/0.99  --qbf_split                             512
% 3.42/0.99  
% 3.42/0.99  ------ BMC1 Options
% 3.42/0.99  
% 3.42/0.99  --bmc1_incremental                      false
% 3.42/0.99  --bmc1_axioms                           reachable_all
% 3.42/0.99  --bmc1_min_bound                        0
% 3.42/0.99  --bmc1_max_bound                        -1
% 3.42/0.99  --bmc1_max_bound_default                -1
% 3.42/1.00  --bmc1_symbol_reachability              true
% 3.42/1.00  --bmc1_property_lemmas                  false
% 3.42/1.00  --bmc1_k_induction                      false
% 3.42/1.00  --bmc1_non_equiv_states                 false
% 3.42/1.00  --bmc1_deadlock                         false
% 3.42/1.00  --bmc1_ucm                              false
% 3.42/1.00  --bmc1_add_unsat_core                   none
% 3.42/1.00  --bmc1_unsat_core_children              false
% 3.42/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/1.00  --bmc1_out_stat                         full
% 3.42/1.00  --bmc1_ground_init                      false
% 3.42/1.00  --bmc1_pre_inst_next_state              false
% 3.42/1.00  --bmc1_pre_inst_state                   false
% 3.42/1.00  --bmc1_pre_inst_reach_state             false
% 3.42/1.00  --bmc1_out_unsat_core                   false
% 3.42/1.00  --bmc1_aig_witness_out                  false
% 3.42/1.00  --bmc1_verbose                          false
% 3.42/1.00  --bmc1_dump_clauses_tptp                false
% 3.42/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.42/1.00  --bmc1_dump_file                        -
% 3.42/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.42/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.42/1.00  --bmc1_ucm_extend_mode                  1
% 3.42/1.00  --bmc1_ucm_init_mode                    2
% 3.42/1.00  --bmc1_ucm_cone_mode                    none
% 3.42/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.42/1.00  --bmc1_ucm_relax_model                  4
% 3.42/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.42/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/1.00  --bmc1_ucm_layered_model                none
% 3.42/1.00  --bmc1_ucm_max_lemma_size               10
% 3.42/1.00  
% 3.42/1.00  ------ AIG Options
% 3.42/1.00  
% 3.42/1.00  --aig_mode                              false
% 3.42/1.00  
% 3.42/1.00  ------ Instantiation Options
% 3.42/1.00  
% 3.42/1.00  --instantiation_flag                    true
% 3.42/1.00  --inst_sos_flag                         false
% 3.42/1.00  --inst_sos_phase                        true
% 3.42/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/1.00  --inst_lit_sel_side                     none
% 3.42/1.00  --inst_solver_per_active                1400
% 3.42/1.00  --inst_solver_calls_frac                1.
% 3.42/1.00  --inst_passive_queue_type               priority_queues
% 3.42/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/1.00  --inst_passive_queues_freq              [25;2]
% 3.42/1.00  --inst_dismatching                      true
% 3.42/1.00  --inst_eager_unprocessed_to_passive     true
% 3.42/1.00  --inst_prop_sim_given                   true
% 3.42/1.00  --inst_prop_sim_new                     false
% 3.42/1.00  --inst_subs_new                         false
% 3.42/1.00  --inst_eq_res_simp                      false
% 3.42/1.00  --inst_subs_given                       false
% 3.42/1.00  --inst_orphan_elimination               true
% 3.42/1.00  --inst_learning_loop_flag               true
% 3.42/1.00  --inst_learning_start                   3000
% 3.42/1.00  --inst_learning_factor                  2
% 3.42/1.00  --inst_start_prop_sim_after_learn       3
% 3.42/1.00  --inst_sel_renew                        solver
% 3.42/1.00  --inst_lit_activity_flag                true
% 3.42/1.00  --inst_restr_to_given                   false
% 3.42/1.00  --inst_activity_threshold               500
% 3.42/1.00  --inst_out_proof                        true
% 3.42/1.00  
% 3.42/1.00  ------ Resolution Options
% 3.42/1.00  
% 3.42/1.00  --resolution_flag                       false
% 3.42/1.00  --res_lit_sel                           adaptive
% 3.42/1.00  --res_lit_sel_side                      none
% 3.42/1.00  --res_ordering                          kbo
% 3.42/1.00  --res_to_prop_solver                    active
% 3.42/1.00  --res_prop_simpl_new                    false
% 3.42/1.00  --res_prop_simpl_given                  true
% 3.42/1.00  --res_passive_queue_type                priority_queues
% 3.42/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/1.00  --res_passive_queues_freq               [15;5]
% 3.42/1.00  --res_forward_subs                      full
% 3.42/1.00  --res_backward_subs                     full
% 3.42/1.00  --res_forward_subs_resolution           true
% 3.42/1.00  --res_backward_subs_resolution          true
% 3.42/1.00  --res_orphan_elimination                true
% 3.42/1.00  --res_time_limit                        2.
% 3.42/1.00  --res_out_proof                         true
% 3.42/1.00  
% 3.42/1.00  ------ Superposition Options
% 3.42/1.00  
% 3.42/1.00  --superposition_flag                    true
% 3.42/1.00  --sup_passive_queue_type                priority_queues
% 3.42/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.42/1.00  --demod_completeness_check              fast
% 3.42/1.00  --demod_use_ground                      true
% 3.42/1.00  --sup_to_prop_solver                    passive
% 3.42/1.00  --sup_prop_simpl_new                    true
% 3.42/1.00  --sup_prop_simpl_given                  true
% 3.42/1.00  --sup_fun_splitting                     false
% 3.42/1.00  --sup_smt_interval                      50000
% 3.42/1.00  
% 3.42/1.00  ------ Superposition Simplification Setup
% 3.42/1.00  
% 3.42/1.00  --sup_indices_passive                   []
% 3.42/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/1.00  --sup_full_bw                           [BwDemod]
% 3.42/1.00  --sup_immed_triv                        [TrivRules]
% 3.42/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/1.00  --sup_immed_bw_main                     []
% 3.42/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/1.00  
% 3.42/1.00  ------ Combination Options
% 3.42/1.00  
% 3.42/1.00  --comb_res_mult                         3
% 3.42/1.00  --comb_sup_mult                         2
% 3.42/1.00  --comb_inst_mult                        10
% 3.42/1.00  
% 3.42/1.00  ------ Debug Options
% 3.42/1.00  
% 3.42/1.00  --dbg_backtrace                         false
% 3.42/1.00  --dbg_dump_prop_clauses                 false
% 3.42/1.00  --dbg_dump_prop_clauses_file            -
% 3.42/1.00  --dbg_out_stat                          false
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  ------ Proving...
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  % SZS status Theorem for theBenchmark.p
% 3.42/1.00  
% 3.42/1.00   Resolution empty clause
% 3.42/1.00  
% 3.42/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/1.00  
% 3.42/1.00  fof(f9,conjecture,(
% 3.42/1.00    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f10,negated_conjecture,(
% 3.42/1.00    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.42/1.00    inference(negated_conjecture,[],[f9])).
% 3.42/1.00  
% 3.42/1.00  fof(f28,plain,(
% 3.42/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f10])).
% 3.42/1.00  
% 3.42/1.00  fof(f29,plain,(
% 3.42/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f28])).
% 3.42/1.00  
% 3.42/1.00  fof(f44,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK8 != X2 & k3_lattices(X0,X1,sK8) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK8) = k4_lattices(X0,X1,X2) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f43,plain,(
% 3.42/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK7 != X3 & k3_lattices(X0,X1,sK7) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK7) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f42,plain,(
% 3.42/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK6,X2) = k3_lattices(X0,sK6,X3) & k4_lattices(X0,sK6,X2) = k4_lattices(X0,sK6,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f41,plain,(
% 3.42/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK5,X1,X2) = k3_lattices(sK5,X1,X3) & k4_lattices(sK5,X1,X2) = k4_lattices(sK5,X1,X3) & m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_subset_1(X1,u1_struct_0(sK5))) & l3_lattices(sK5) & v11_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f45,plain,(
% 3.42/1.00    (((sK7 != sK8 & k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) & k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l3_lattices(sK5) & v11_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f29,f44,f43,f42,f41])).
% 3.42/1.00  
% 3.42/1.00  fof(f72,plain,(
% 3.42/1.00    m1_subset_1(sK8,u1_struct_0(sK5))),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f70,plain,(
% 3.42/1.00    m1_subset_1(sK6,u1_struct_0(sK5))),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f71,plain,(
% 3.42/1.00    m1_subset_1(sK7,u1_struct_0(sK5))),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f3,axiom,(
% 3.42/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)))))))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f17,plain,(
% 3.42/1.00    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f3])).
% 3.42/1.00  
% 3.42/1.00  fof(f18,plain,(
% 3.42/1.00    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f17])).
% 3.42/1.00  
% 3.42/1.00  fof(f30,plain,(
% 3.42/1.00    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(nnf_transformation,[],[f18])).
% 3.42/1.00  
% 3.42/1.00  fof(f31,plain,(
% 3.42/1.00    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(rectify,[],[f30])).
% 3.42/1.00  
% 3.42/1.00  fof(f34,plain,(
% 3.42/1.00    ( ! [X2,X1] : (! [X0] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f33,plain,(
% 3.42/1.00    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f32,plain,(
% 3.42/1.00    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f35,plain,(
% 3.42/1.00    ! [X0] : (((v11_lattices(X0) | (((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 3.42/1.00  
% 3.42/1.00  fof(f52,plain,(
% 3.42/1.00    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f35])).
% 3.42/1.00  
% 3.42/1.00  fof(f66,plain,(
% 3.42/1.00    ~v2_struct_0(sK5)),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f68,plain,(
% 3.42/1.00    v11_lattices(sK5)),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f69,plain,(
% 3.42/1.00    l3_lattices(sK5)),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f5,axiom,(
% 3.42/1.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f21,plain,(
% 3.42/1.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.42/1.00    inference(ennf_transformation,[],[f5])).
% 3.42/1.00  
% 3.42/1.00  fof(f61,plain,(
% 3.42/1.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f21])).
% 3.42/1.00  
% 3.42/1.00  fof(f7,axiom,(
% 3.42/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f24,plain,(
% 3.42/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f7])).
% 3.42/1.00  
% 3.42/1.00  fof(f25,plain,(
% 3.42/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f24])).
% 3.42/1.00  
% 3.42/1.00  fof(f64,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f25])).
% 3.42/1.00  
% 3.42/1.00  fof(f1,axiom,(
% 3.42/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f11,plain,(
% 3.42/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.42/1.00    inference(pure_predicate_removal,[],[f1])).
% 3.42/1.00  
% 3.42/1.00  fof(f12,plain,(
% 3.42/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.42/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.42/1.00  
% 3.42/1.00  fof(f13,plain,(
% 3.42/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.42/1.00    inference(ennf_transformation,[],[f12])).
% 3.42/1.00  
% 3.42/1.00  fof(f14,plain,(
% 3.42/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.42/1.00    inference(flattening,[],[f13])).
% 3.42/1.00  
% 3.42/1.00  fof(f48,plain,(
% 3.42/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f14])).
% 3.42/1.00  
% 3.42/1.00  fof(f67,plain,(
% 3.42/1.00    v10_lattices(sK5)),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f47,plain,(
% 3.42/1.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f14])).
% 3.42/1.00  
% 3.42/1.00  fof(f62,plain,(
% 3.42/1.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f21])).
% 3.42/1.00  
% 3.42/1.00  fof(f6,axiom,(
% 3.42/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f22,plain,(
% 3.42/1.00    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f6])).
% 3.42/1.00  
% 3.42/1.00  fof(f23,plain,(
% 3.42/1.00    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f22])).
% 3.42/1.00  
% 3.42/1.00  fof(f63,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f23])).
% 3.42/1.00  
% 3.42/1.00  fof(f74,plain,(
% 3.42/1.00    k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8)),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f2,axiom,(
% 3.42/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f15,plain,(
% 3.42/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f2])).
% 3.42/1.00  
% 3.42/1.00  fof(f16,plain,(
% 3.42/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f15])).
% 3.42/1.00  
% 3.42/1.00  fof(f51,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f16])).
% 3.42/1.00  
% 3.42/1.00  fof(f73,plain,(
% 3.42/1.00    k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8)),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  fof(f50,plain,(
% 3.42/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f14])).
% 3.42/1.00  
% 3.42/1.00  fof(f8,axiom,(
% 3.42/1.00    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,X1,X1) = X1))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f26,plain,(
% 3.42/1.00    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f8])).
% 3.42/1.00  
% 3.42/1.00  fof(f27,plain,(
% 3.42/1.00    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f26])).
% 3.42/1.00  
% 3.42/1.00  fof(f65,plain,(
% 3.42/1.00    ( ! [X0,X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f27])).
% 3.42/1.00  
% 3.42/1.00  fof(f49,plain,(
% 3.42/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f14])).
% 3.42/1.00  
% 3.42/1.00  fof(f4,axiom,(
% 3.42/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f19,plain,(
% 3.42/1.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.42/1.00    inference(ennf_transformation,[],[f4])).
% 3.42/1.00  
% 3.42/1.00  fof(f20,plain,(
% 3.42/1.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(flattening,[],[f19])).
% 3.42/1.00  
% 3.42/1.00  fof(f36,plain,(
% 3.42/1.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(nnf_transformation,[],[f20])).
% 3.42/1.00  
% 3.42/1.00  fof(f37,plain,(
% 3.42/1.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(rectify,[],[f36])).
% 3.42/1.00  
% 3.42/1.00  fof(f39,plain,(
% 3.42/1.00    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f38,plain,(
% 3.42/1.00    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f40,plain,(
% 3.42/1.00    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f39,f38])).
% 3.42/1.00  
% 3.42/1.00  fof(f57,plain,(
% 3.42/1.00    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f40])).
% 3.42/1.00  
% 3.42/1.00  fof(f75,plain,(
% 3.42/1.00    sK7 != sK8),
% 3.42/1.00    inference(cnf_transformation,[],[f45])).
% 3.42/1.00  
% 3.42/1.00  cnf(c_23,negated_conjecture,
% 3.42/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.42/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_818,negated_conjecture,
% 3.42/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_990,plain,
% 3.42/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_25,negated_conjecture,
% 3.42/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.42/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_816,negated_conjecture,
% 3.42/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_992,plain,
% 3.42/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_24,negated_conjecture,
% 3.42/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.42/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_817,negated_conjecture,
% 3.42/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_991,plain,
% 3.42/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_10,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.42/1.00      | ~ v11_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
% 3.42/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_29,negated_conjecture,
% 3.42/1.00      ( ~ v2_struct_0(sK5) ),
% 3.42/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_713,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.42/1.00      | ~ v11_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_714,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.42/1.00      | ~ v11_lattices(sK5)
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_713]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_27,negated_conjecture,
% 3.42/1.00      ( v11_lattices(sK5) ),
% 3.42/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_26,negated_conjecture,
% 3.42/1.00      ( l3_lattices(sK5) ),
% 3.42/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_718,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_714,c_27,c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_719,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X1,X2),k2_lattices(sK5,X1,X0)) = k2_lattices(sK5,X1,k1_lattices(sK5,X2,X0)) ),
% 3.42/1.00      inference(renaming,[status(thm)],[c_718]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_810,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X2_53,u1_struct_0(sK5))
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X1_53,X2_53),k2_lattices(sK5,X1_53,X0_53)) = k2_lattices(sK5,X1_53,k1_lattices(sK5,X2_53,X0_53)) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_719]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_998,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,X0_53,X1_53),k2_lattices(sK5,X0_53,X2_53)) = k2_lattices(sK5,X0_53,k1_lattices(sK5,X1_53,X2_53))
% 3.42/1.00      | m1_subset_1(X2_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2922,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK7,X0_53),k2_lattices(sK5,sK7,X1_53)) = k2_lattices(sK5,sK7,k1_lattices(sK5,X0_53,X1_53))
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_998]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_4066,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,X0_53)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,X0_53))
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_2922]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_16,plain,
% 3.42/1.00      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_18,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l1_lattices(X1)
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_382,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X3)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | X1 != X3
% 3.42/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_383,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_382]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2,plain,
% 3.42/1.00      ( v6_lattices(X0)
% 3.42/1.00      | ~ l3_lattices(X0)
% 3.42/1.00      | v2_struct_0(X0)
% 3.42/1.00      | ~ v10_lattices(X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_28,negated_conjecture,
% 3.42/1.00      ( v10_lattices(sK5) ),
% 3.42/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_444,plain,
% 3.42/1.00      ( v6_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK5 != X0 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_445,plain,
% 3.42/1.00      ( v6_lattices(sK5) | ~ l3_lattices(sK5) | v2_struct_0(sK5) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_444]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_79,plain,
% 3.42/1.00      ( v6_lattices(sK5)
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | ~ v10_lattices(sK5) ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_447,plain,
% 3.42/1.00      ( v6_lattices(sK5) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_445,c_29,c_28,c_26,c_79]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_537,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_383,c_447]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_538,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | k2_lattices(sK5,X1,X0) = k4_lattices(sK5,X1,X0) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_542,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | k2_lattices(sK5,X1,X0) = k4_lattices(sK5,X1,X0) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_538,c_29,c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_812,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 3.42/1.00      | k2_lattices(sK5,X1_53,X0_53) = k4_lattices(sK5,X1_53,X0_53) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_542]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_996,plain,
% 3.42/1.00      ( k2_lattices(sK5,X0_53,X1_53) = k4_lattices(sK5,X0_53,X1_53)
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2260,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,X0_53) = k4_lattices(sK5,sK7,X0_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_996]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2426,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK7,sK6) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_2260]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_4069,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,X0_53)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,X0_53))
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_4066,c_2426]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7512,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK8)) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_4069]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3,plain,
% 3.42/1.00      ( v4_lattices(X0)
% 3.42/1.00      | ~ l3_lattices(X0)
% 3.42/1.00      | v2_struct_0(X0)
% 3.42/1.00      | ~ v10_lattices(X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_15,plain,
% 3.42/1.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_17,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l2_lattices(X1)
% 3.42/1.00      | ~ v4_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_286,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v4_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X3)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | X1 != X3
% 3.42/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_287,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v4_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_317,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X3)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X3)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | ~ v10_lattices(X3)
% 3.42/1.00      | X1 != X3
% 3.42/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_287]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_318,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | ~ v10_lattices(X1)
% 3.42/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_484,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_318]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_485,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | k3_lattices(sK5,X0,X1) = k1_lattices(sK5,X0,X1) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_484]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_489,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | k3_lattices(sK5,X0,X1) = k1_lattices(sK5,X0,X1) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_485,c_29,c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_814,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 3.42/1.00      | k3_lattices(sK5,X0_53,X1_53) = k1_lattices(sK5,X0_53,X1_53) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_489]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_994,plain,
% 3.42/1.00      ( k3_lattices(sK5,X0_53,X1_53) = k1_lattices(sK5,X0_53,X1_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1258,plain,
% 3.42/1.00      ( k3_lattices(sK5,sK6,X0_53) = k1_lattices(sK5,sK6,X0_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_994]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1512,plain,
% 3.42/1.00      ( k3_lattices(sK5,sK6,sK7) = k1_lattices(sK5,sK6,sK7) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_1258]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1511,plain,
% 3.42/1.00      ( k3_lattices(sK5,sK6,sK8) = k1_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_1258]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_21,negated_conjecture,
% 3.42/1.00      ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_820,negated_conjecture,
% 3.42/1.00      ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1539,plain,
% 3.42/1.00      ( k3_lattices(sK5,sK6,sK7) = k1_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_1511,c_820]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1592,plain,
% 3.42/1.00      ( k1_lattices(sK5,sK6,sK7) = k1_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_1512,c_1539]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2424,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,sK8) = k4_lattices(sK5,sK7,sK8) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_2260]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2259,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,X0_53) = k4_lattices(sK5,sK8,X0_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_996]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2286,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK8,sK6) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_2259]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_5,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l1_lattices(X1)
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_406,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X3)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | X1 != X3
% 3.42/1.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_5]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_407,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_406]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_516,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_407,c_447]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_517,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | k4_lattices(sK5,X1,X0) = k4_lattices(sK5,X0,X1) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_521,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | k4_lattices(sK5,X1,X0) = k4_lattices(sK5,X0,X1) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_517,c_29,c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_813,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 3.42/1.00      | k4_lattices(sK5,X1_53,X0_53) = k4_lattices(sK5,X0_53,X1_53) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_521]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_995,plain,
% 3.42/1.00      ( k4_lattices(sK5,X0_53,X1_53) = k4_lattices(sK5,X1_53,X0_53)
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1545,plain,
% 3.42/1.00      ( k4_lattices(sK5,X0_53,sK7) = k4_lattices(sK5,sK7,X0_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_995]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1989,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_1545]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1544,plain,
% 3.42/1.00      ( k4_lattices(sK5,X0_53,sK8) = k4_lattices(sK5,sK8,X0_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_995]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1821,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_1544]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_22,negated_conjecture,
% 3.42/1.00      ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_819,negated_conjecture,
% 3.42/1.00      ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1893,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK7) ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_1821,c_819]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1993,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK8,sK6) ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_1989,c_1893]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2288,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK7,sK6) ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_2286,c_1993]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2921,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,X0_53),k2_lattices(sK5,sK8,X1_53)) = k2_lattices(sK5,sK8,k1_lattices(sK5,X0_53,X1_53))
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_998]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3401,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,X0_53)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,X0_53))
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_2921]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3949,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,sK7)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_3401]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_5633,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK8,sK7)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_2288,c_3949]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2285,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK8,sK7) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_2259]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1820,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK7,sK8) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_1544]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2291,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK7,sK8) ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_2285,c_1820]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3948,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,sK8)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK8)) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_3401]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3956,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK6),k2_lattices(sK5,sK8,sK8)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_3948,c_1592]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2284,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,sK8) = k4_lattices(sK5,sK8,sK8) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_2259]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_0,plain,
% 3.42/1.00      ( ~ l3_lattices(X0)
% 3.42/1.00      | v2_struct_0(X0)
% 3.42/1.00      | ~ v10_lattices(X0)
% 3.42/1.00      | v9_lattices(X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_19,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ v8_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | ~ v9_lattices(X1)
% 3.42/1.00      | k4_lattices(X1,X0,X0) = X0 ),
% 3.42/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_348,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ v8_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X2)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X2)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | ~ v10_lattices(X2)
% 3.42/1.00      | X1 != X2
% 3.42/1.00      | k4_lattices(X1,X0,X0) = X0 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_349,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ v6_lattices(X1)
% 3.42/1.00      | ~ v8_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | ~ v10_lattices(X1)
% 3.42/1.00      | k4_lattices(X1,X0,X0) = X0 ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_348]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1,plain,
% 3.42/1.00      ( v8_lattices(X0)
% 3.42/1.00      | ~ l3_lattices(X0)
% 3.42/1.00      | v2_struct_0(X0)
% 3.42/1.00      | ~ v10_lattices(X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_367,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | ~ v10_lattices(X1)
% 3.42/1.00      | k4_lattices(X1,X0,X0) = X0 ),
% 3.42/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_349,c_1,c_2]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_466,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k4_lattices(X1,X0,X0) = X0
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_367]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_467,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | k4_lattices(sK5,X0,X0) = X0 ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_466]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_471,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5)) | k4_lattices(sK5,X0,X0) = X0 ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_467,c_29,c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_815,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 3.42/1.00      | k4_lattices(sK5,X0_53,X0_53) = X0_53 ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_471]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_993,plain,
% 3.42/1.00      ( k4_lattices(sK5,X0_53,X0_53) = X0_53
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1162,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK8,sK8) = sK8 ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_993]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2294,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,sK8) = sK8 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_2284,c_1162]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_14,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v8_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 3.42/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_694,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ v8_lattices(X1)
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_695,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ v8_lattices(sK5)
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_694]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_455,plain,
% 3.42/1.00      ( v8_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK5 != X0 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_456,plain,
% 3.42/1.00      ( v8_lattices(sK5) | ~ l3_lattices(sK5) | v2_struct_0(sK5) ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_82,plain,
% 3.42/1.00      ( v8_lattices(sK5)
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | ~ v10_lattices(sK5) ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_458,plain,
% 3.42/1.00      ( v8_lattices(sK5) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_456,c_29,c_28,c_26,c_82]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_638,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.42/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.42/1.00      | ~ l3_lattices(X1)
% 3.42/1.00      | v2_struct_0(X1)
% 3.42/1.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.42/1.00      | sK5 != X1 ),
% 3.42/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_458]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_639,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | ~ l3_lattices(sK5)
% 3.42/1.00      | v2_struct_0(sK5)
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
% 3.42/1.00      inference(unflattening,[status(thm)],[c_638]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_699,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_695,c_29,c_26,c_639]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_811,plain,
% 3.42/1.00      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 3.42/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 3.42/1.00      | k1_lattices(sK5,k2_lattices(sK5,X1_53,X0_53),X0_53) = X0_53 ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_699]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_997,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,X0_53,X1_53),X1_53) = X1_53
% 3.42/1.00      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2601,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_53),X0_53) = X0_53
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_997]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3060,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),sK8) = sK8 ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_2601]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2261,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK6,X0_53) = k4_lattices(sK5,sK6,X0_53)
% 3.42/1.00      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_992,c_996]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2545,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK6,sK8) = k4_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_990,c_2261]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3068,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK6,sK8),sK8) = sK8 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_3060,c_2545]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2175,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK8) ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_1993,c_1821]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_5973,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),sK8) = sK8 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_3068,c_2175]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_6539,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK8,k1_lattices(sK5,sK6,sK7)) = sK8 ),
% 3.42/1.00      inference(light_normalisation,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_3956,c_2288,c_2294,c_5973]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_6935,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k4_lattices(sK5,sK7,sK8)) = sK8 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_5633,c_2291,c_6539]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7521,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK7)) = sK8 ),
% 3.42/1.00      inference(light_normalisation,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_7512,c_1592,c_2424,c_6935]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7513,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),k2_lattices(sK5,sK7,sK7)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK7)) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_4069]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2425,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,sK7) = k4_lattices(sK5,sK7,sK7) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_2260]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1163,plain,
% 3.42/1.00      ( k4_lattices(sK5,sK7,sK7) = sK7 ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_993]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2430,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,sK7) = sK7 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_2425,c_1163]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2546,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK7) ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_2261]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2552,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK7,sK6) ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_2546,c_1989]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3061,plain,
% 3.42/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK7),sK7) = sK7 ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_991,c_2601]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_5851,plain,
% 3.42/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK6),sK7) = sK7 ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_2552,c_3061]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7518,plain,
% 3.42/1.00      ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK6,sK7)) = sK7 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_7513,c_2430,c_5851]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7636,plain,
% 3.42/1.00      ( sK8 = sK7 ),
% 3.42/1.00      inference(light_normalisation,[status(thm)],[c_7521,c_7518]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_20,negated_conjecture,
% 3.42/1.00      ( sK7 != sK8 ),
% 3.42/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_821,negated_conjecture,
% 3.42/1.00      ( sK7 != sK8 ),
% 3.42/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7673,plain,
% 3.42/1.00      ( sK7 != sK7 ),
% 3.42/1.00      inference(demodulation,[status(thm)],[c_7636,c_821]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7674,plain,
% 3.42/1.00      ( $false ),
% 3.42/1.00      inference(equality_resolution_simp,[status(thm)],[c_7673]) ).
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/1.00  
% 3.42/1.00  ------                               Statistics
% 3.42/1.00  
% 3.42/1.00  ------ General
% 3.42/1.00  
% 3.42/1.00  abstr_ref_over_cycles:                  0
% 3.42/1.00  abstr_ref_under_cycles:                 0
% 3.42/1.00  gc_basic_clause_elim:                   0
% 3.42/1.00  forced_gc_time:                         0
% 3.42/1.00  parsing_time:                           0.012
% 3.42/1.00  unif_index_cands_time:                  0.
% 3.42/1.00  unif_index_add_time:                    0.
% 3.42/1.00  orderings_time:                         0.
% 3.42/1.00  out_proof_time:                         0.01
% 3.42/1.00  total_time:                             0.308
% 3.42/1.00  num_of_symbols:                         56
% 3.42/1.00  num_of_terms:                           10715
% 3.42/1.00  
% 3.42/1.00  ------ Preprocessing
% 3.42/1.00  
% 3.42/1.00  num_of_splits:                          0
% 3.42/1.00  num_of_split_atoms:                     0
% 3.42/1.00  num_of_reused_defs:                     0
% 3.42/1.00  num_eq_ax_congr_red:                    21
% 3.42/1.00  num_of_sem_filtered_clauses:            1
% 3.42/1.00  num_of_subtypes:                        3
% 3.42/1.00  monotx_restored_types:                  0
% 3.42/1.00  sat_num_of_epr_types:                   0
% 3.42/1.00  sat_num_of_non_cyclic_types:            0
% 3.42/1.00  sat_guarded_non_collapsed_types:        1
% 3.42/1.00  num_pure_diseq_elim:                    0
% 3.42/1.00  simp_replaced_by:                       0
% 3.42/1.00  res_preprocessed:                       80
% 3.42/1.00  prep_upred:                             0
% 3.42/1.00  prep_unflattend:                        24
% 3.42/1.00  smt_new_axioms:                         0
% 3.42/1.00  pred_elim_cands:                        1
% 3.42/1.00  pred_elim:                              10
% 3.42/1.00  pred_elim_cl:                           17
% 3.42/1.00  pred_elim_cycles:                       13
% 3.42/1.00  merged_defs:                            0
% 3.42/1.00  merged_defs_ncl:                        0
% 3.42/1.00  bin_hyper_res:                          0
% 3.42/1.00  prep_cycles:                            4
% 3.42/1.00  pred_elim_time:                         0.009
% 3.42/1.00  splitting_time:                         0.
% 3.42/1.00  sem_filter_time:                        0.
% 3.42/1.00  monotx_time:                            0.
% 3.42/1.00  subtype_inf_time:                       0.
% 3.42/1.00  
% 3.42/1.00  ------ Problem properties
% 3.42/1.00  
% 3.42/1.00  clauses:                                12
% 3.42/1.00  conjectures:                            6
% 3.42/1.00  epr:                                    1
% 3.42/1.00  horn:                                   12
% 3.42/1.00  ground:                                 6
% 3.42/1.00  unary:                                  6
% 3.42/1.00  binary:                                 1
% 3.42/1.00  lits:                                   24
% 3.42/1.00  lits_eq:                                9
% 3.42/1.00  fd_pure:                                0
% 3.42/1.00  fd_pseudo:                              0
% 3.42/1.00  fd_cond:                                0
% 3.42/1.00  fd_pseudo_cond:                         0
% 3.42/1.00  ac_symbols:                             0
% 3.42/1.00  
% 3.42/1.00  ------ Propositional Solver
% 3.42/1.00  
% 3.42/1.00  prop_solver_calls:                      31
% 3.42/1.00  prop_fast_solver_calls:                 693
% 3.42/1.00  smt_solver_calls:                       0
% 3.42/1.00  smt_fast_solver_calls:                  0
% 3.42/1.00  prop_num_of_clauses:                    4269
% 3.42/1.00  prop_preprocess_simplified:             8731
% 3.42/1.00  prop_fo_subsumed:                       18
% 3.42/1.00  prop_solver_time:                       0.
% 3.42/1.00  smt_solver_time:                        0.
% 3.42/1.00  smt_fast_solver_time:                   0.
% 3.42/1.00  prop_fast_solver_time:                  0.
% 3.42/1.00  prop_unsat_core_time:                   0.
% 3.42/1.00  
% 3.42/1.00  ------ QBF
% 3.42/1.00  
% 3.42/1.00  qbf_q_res:                              0
% 3.42/1.00  qbf_num_tautologies:                    0
% 3.42/1.00  qbf_prep_cycles:                        0
% 3.42/1.00  
% 3.42/1.00  ------ BMC1
% 3.42/1.00  
% 3.42/1.00  bmc1_current_bound:                     -1
% 3.42/1.00  bmc1_last_solved_bound:                 -1
% 3.42/1.00  bmc1_unsat_core_size:                   -1
% 3.42/1.00  bmc1_unsat_core_parents_size:           -1
% 3.42/1.00  bmc1_merge_next_fun:                    0
% 3.42/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.42/1.00  
% 3.42/1.00  ------ Instantiation
% 3.42/1.00  
% 3.42/1.00  inst_num_of_clauses:                    2034
% 3.42/1.00  inst_num_in_passive:                    891
% 3.42/1.00  inst_num_in_active:                     508
% 3.42/1.00  inst_num_in_unprocessed:                635
% 3.42/1.00  inst_num_of_loops:                      570
% 3.42/1.00  inst_num_of_learning_restarts:          0
% 3.42/1.00  inst_num_moves_active_passive:          55
% 3.42/1.00  inst_lit_activity:                      0
% 3.42/1.00  inst_lit_activity_moves:                0
% 3.42/1.00  inst_num_tautologies:                   0
% 3.42/1.00  inst_num_prop_implied:                  0
% 3.42/1.00  inst_num_existing_simplified:           0
% 3.42/1.00  inst_num_eq_res_simplified:             0
% 3.42/1.00  inst_num_child_elim:                    0
% 3.42/1.00  inst_num_of_dismatching_blockings:      573
% 3.42/1.00  inst_num_of_non_proper_insts:           1749
% 3.42/1.00  inst_num_of_duplicates:                 0
% 3.42/1.00  inst_inst_num_from_inst_to_res:         0
% 3.42/1.00  inst_dismatching_checking_time:         0.
% 3.42/1.00  
% 3.42/1.00  ------ Resolution
% 3.42/1.00  
% 3.42/1.00  res_num_of_clauses:                     0
% 3.42/1.00  res_num_in_passive:                     0
% 3.42/1.00  res_num_in_active:                      0
% 3.42/1.00  res_num_of_loops:                       84
% 3.42/1.00  res_forward_subset_subsumed:            68
% 3.42/1.00  res_backward_subset_subsumed:           2
% 3.42/1.00  res_forward_subsumed:                   0
% 3.42/1.00  res_backward_subsumed:                  0
% 3.42/1.00  res_forward_subsumption_resolution:     2
% 3.42/1.00  res_backward_subsumption_resolution:    0
% 3.42/1.00  res_clause_to_clause_subsumption:       265
% 3.42/1.00  res_orphan_elimination:                 0
% 3.42/1.00  res_tautology_del:                      104
% 3.42/1.00  res_num_eq_res_simplified:              0
% 3.42/1.00  res_num_sel_changes:                    0
% 3.42/1.00  res_moves_from_active_to_pass:          0
% 3.42/1.00  
% 3.42/1.00  ------ Superposition
% 3.42/1.00  
% 3.42/1.00  sup_time_total:                         0.
% 3.42/1.00  sup_time_generating:                    0.
% 3.42/1.00  sup_time_sim_full:                      0.
% 3.42/1.00  sup_time_sim_immed:                     0.
% 3.42/1.00  
% 3.42/1.00  sup_num_of_clauses:                     49
% 3.42/1.00  sup_num_in_active:                      41
% 3.42/1.00  sup_num_in_passive:                     8
% 3.42/1.00  sup_num_of_loops:                       112
% 3.42/1.00  sup_fw_superposition:                   93
% 3.42/1.00  sup_bw_superposition:                   0
% 3.42/1.00  sup_immediate_simplified:               32
% 3.42/1.00  sup_given_eliminated:                   0
% 3.42/1.00  comparisons_done:                       0
% 3.42/1.00  comparisons_avoided:                    0
% 3.42/1.00  
% 3.42/1.00  ------ Simplifications
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  sim_fw_subset_subsumed:                 0
% 3.42/1.00  sim_bw_subset_subsumed:                 0
% 3.42/1.00  sim_fw_subsumed:                        3
% 3.42/1.00  sim_bw_subsumed:                        0
% 3.42/1.00  sim_fw_subsumption_res:                 0
% 3.42/1.00  sim_bw_subsumption_res:                 0
% 3.42/1.00  sim_tautology_del:                      0
% 3.42/1.00  sim_eq_tautology_del:                   12
% 3.42/1.00  sim_eq_res_simp:                        0
% 3.42/1.00  sim_fw_demodulated:                     0
% 3.42/1.00  sim_bw_demodulated:                     71
% 3.42/1.00  sim_light_normalised:                   46
% 3.42/1.00  sim_joinable_taut:                      0
% 3.42/1.00  sim_joinable_simp:                      0
% 3.42/1.00  sim_ac_normalised:                      0
% 3.42/1.00  sim_smt_subsumption:                    0
% 3.42/1.00  
%------------------------------------------------------------------------------

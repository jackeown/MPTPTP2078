%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:15 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  216 (3882 expanded)
%              Number of clauses        :  140 ( 811 expanded)
%              Number of leaves         :   21 (1374 expanded)
%              Depth                    :   24
%              Number of atoms          :  895 (31310 expanded)
%              Number of equality atoms :  265 (10453 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK10 != X2
        & k3_lattices(X0,X1,sK10) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK10) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK9 != X3
            & k3_lattices(X0,X1,sK9) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK9) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                & k3_lattices(X0,sK8,X2) = k3_lattices(X0,sK8,X3)
                & k4_lattices(X0,sK8,X2) = k4_lattices(X0,sK8,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
                  & k3_lattices(sK7,X1,X2) = k3_lattices(sK7,X1,X3)
                  & k4_lattices(sK7,X1,X2) = k4_lattices(sK7,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK7)) )
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l3_lattices(sK7)
      & v11_lattices(sK7)
      & v10_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( sK9 != sK10
    & k3_lattices(sK7,sK8,sK9) = k3_lattices(sK7,sK8,sK10)
    & k4_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK10)
    & m1_subset_1(sK10,u1_struct_0(sK7))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l3_lattices(sK7)
    & v11_lattices(sK7)
    & v10_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f34,f54,f53,f52,f51])).

fof(f87,plain,(
    m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f63,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v11_lattices(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
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

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f59,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    k4_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK6(X0))) != X1
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) != sK5(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != sK5(X0)
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f47,f49,f48])).

fof(f72,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f58,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    k3_lattices(sK7,sK8,sK9) = k3_lattices(sK7,sK8,sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).

fof(f68,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    sK9 != sK10 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1325,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1323,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1041,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_34])).

cnf(c_1042,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v11_lattices(sK7)
    | ~ l3_lattices(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X2,X0),k2_lattices(sK7,X2,X1)) = k2_lattices(sK7,X2,k1_lattices(sK7,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_1041])).

cnf(c_31,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,negated_conjecture,
    ( v11_lattices(sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X2,X0),k2_lattices(sK7,X2,X1)) = k2_lattices(sK7,X2,k1_lattices(sK7,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X2,X0),k2_lattices(sK7,X2,X1)) = k2_lattices(sK7,X2,k1_lattices(sK7,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1042,c_34,c_31,c_928])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),k2_lattices(sK7,X0,X2)) = k2_lattices(sK7,X0,k1_lattices(sK7,X1,X2)) ),
    inference(renaming,[status(thm)],[c_1044])).

cnf(c_1316,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,X0,X1),k2_lattices(sK7,X0,X2)) = k2_lattices(sK7,X0,k1_lattices(sK7,X1,X2))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_1798,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK10,X0),k2_lattices(sK7,sK10,X1)) = k2_lattices(sK7,sK10,k1_lattices(sK7,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1316])).

cnf(c_6009,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK10,sK8),k2_lattices(sK7,sK10,X0)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,X0))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1798])).

cnf(c_21,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,negated_conjecture,
    ( v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_456,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_33])).

cnf(c_457,plain,
    ( v6_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_96,plain,
    ( v6_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_459,plain,
    ( v6_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_34,c_33,c_31,c_96])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_395,c_459])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,X1) = k4_lattices(sK7,X0,X1) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,X1) = k4_lattices(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_34,c_31])).

cnf(c_1320,plain,
    ( k2_lattices(sK7,X0,X1) = k4_lattices(sK7,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_3847,plain,
    ( k2_lattices(sK7,sK10,X0) = k4_lattices(sK7,sK10,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1320])).

cnf(c_3955,plain,
    ( k2_lattices(sK7,sK10,sK8) = k4_lattices(sK7,sK10,sK8) ),
    inference(superposition,[status(thm)],[c_1323,c_3847])).

cnf(c_6012,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK10,sK8),k2_lattices(sK7,sK10,X0)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,X0))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6009,c_3955])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1324,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_6])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_419,c_459])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k4_lattices(sK7,X0,X1) = k4_lattices(sK7,X1,X0) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k4_lattices(sK7,X0,X1) = k4_lattices(sK7,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_34,c_31])).

cnf(c_1321,plain,
    ( k4_lattices(sK7,X0,X1) = k4_lattices(sK7,X1,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_4156,plain,
    ( k4_lattices(sK7,X0,sK9) = k4_lattices(sK7,sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1321])).

cnf(c_6000,plain,
    ( k4_lattices(sK7,sK9,sK8) = k4_lattices(sK7,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1323,c_4156])).

cnf(c_4155,plain,
    ( k4_lattices(sK7,X0,sK10) = k4_lattices(sK7,sK10,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1321])).

cnf(c_5199,plain,
    ( k4_lattices(sK7,sK10,sK8) = k4_lattices(sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_1323,c_4155])).

cnf(c_27,negated_conjecture,
    ( k4_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK10) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5590,plain,
    ( k4_lattices(sK7,sK10,sK8) = k4_lattices(sK7,sK8,sK9) ),
    inference(demodulation,[status(thm)],[c_5199,c_27])).

cnf(c_6034,plain,
    ( k4_lattices(sK7,sK9,sK8) = k4_lattices(sK7,sK10,sK8) ),
    inference(demodulation,[status(thm)],[c_6000,c_5590])).

cnf(c_7275,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK10,X0)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,X0))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6012,c_6034])).

cnf(c_7281,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK10,sK10)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK10)) ),
    inference(superposition,[status(thm)],[c_1325,c_7275])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_459])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v8_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v9_lattices(sK7)
    | k1_lattices(sK7,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_99,plain,
    ( v8_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_102,plain,
    ( ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7)
    | v9_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k1_lattices(sK7,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_34,c_33,c_31,c_99,c_102])).

cnf(c_1319,plain,
    ( k1_lattices(sK7,X0,X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_2692,plain,
    ( k1_lattices(sK7,sK10,sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_1325,c_1319])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v9_lattices(sK7)
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_1003])).

cnf(c_478,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_33])).

cnf(c_479,plain,
    ( ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | v9_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( v9_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_34,c_33,c_31,c_102])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_481])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1004,c_34,c_31,c_664])).

cnf(c_1318,plain,
    ( k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_2082,plain,
    ( k2_lattices(sK7,sK10,k1_lattices(sK7,sK10,X0)) = sK10
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1318])).

cnf(c_2214,plain,
    ( k2_lattices(sK7,sK10,k1_lattices(sK7,sK10,sK10)) = sK10 ),
    inference(superposition,[status(thm)],[c_1325,c_2082])).

cnf(c_3317,plain,
    ( k2_lattices(sK7,sK10,sK10) = sK10 ),
    inference(demodulation,[status(thm)],[c_2692,c_2214])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_333])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_364])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k3_lattices(sK7,X1,X0) = k1_lattices(sK7,X1,X0) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k3_lattices(sK7,X1,X0) = k1_lattices(sK7,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_34,c_31])).

cnf(c_1322,plain,
    ( k3_lattices(sK7,X0,X1) = k1_lattices(sK7,X0,X1)
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_3559,plain,
    ( k3_lattices(sK7,sK8,X0) = k1_lattices(sK7,sK8,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1322])).

cnf(c_3834,plain,
    ( k3_lattices(sK7,sK8,sK9) = k1_lattices(sK7,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1324,c_3559])).

cnf(c_3833,plain,
    ( k3_lattices(sK7,sK8,sK10) = k1_lattices(sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_1325,c_3559])).

cnf(c_26,negated_conjecture,
    ( k3_lattices(sK7,sK8,sK9) = k3_lattices(sK7,sK8,sK10) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3872,plain,
    ( k3_lattices(sK7,sK8,sK9) = k1_lattices(sK7,sK8,sK10) ),
    inference(demodulation,[status(thm)],[c_3833,c_26])).

cnf(c_3939,plain,
    ( k1_lattices(sK7,sK8,sK9) = k1_lattices(sK7,sK8,sK10) ),
    inference(demodulation,[status(thm)],[c_3834,c_3872])).

cnf(c_3849,plain,
    ( k2_lattices(sK7,sK8,X0) = k4_lattices(sK7,sK8,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1320])).

cnf(c_4518,plain,
    ( k2_lattices(sK7,sK8,sK10) = k4_lattices(sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_1325,c_3849])).

cnf(c_4527,plain,
    ( k2_lattices(sK7,sK8,sK10) = k4_lattices(sK7,sK8,sK9) ),
    inference(light_normalisation,[status(thm)],[c_4518,c_27])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1022,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v8_lattices(sK7)
    | ~ l3_lattices(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_1022])).

cnf(c_467,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_33])).

cnf(c_468,plain,
    ( v8_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_470,plain,
    ( v8_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_34,c_33,c_31,c_99])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_470])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1023,c_34,c_31,c_778])).

cnf(c_1317,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_1637,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,X0),X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1317])).

cnf(c_1985,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_1325,c_1637])).

cnf(c_4530,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK8,sK9),sK10) = sK10 ),
    inference(demodulation,[status(thm)],[c_4527,c_1985])).

cnf(c_5592,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK10,sK8),sK10) = sK10 ),
    inference(demodulation,[status(thm)],[c_5590,c_4530])).

cnf(c_6058,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),sK10) = sK10 ),
    inference(demodulation,[status(thm)],[c_6034,c_5592])).

cnf(c_7290,plain,
    ( k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK9)) = sK10 ),
    inference(light_normalisation,[status(thm)],[c_7281,c_3317,c_3939,c_6058])).

cnf(c_7282,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK10,sK9)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK9)) ),
    inference(superposition,[status(thm)],[c_1324,c_7275])).

cnf(c_5198,plain,
    ( k4_lattices(sK7,sK9,sK10) = k4_lattices(sK7,sK10,sK9) ),
    inference(superposition,[status(thm)],[c_1324,c_4155])).

cnf(c_3954,plain,
    ( k2_lattices(sK7,sK10,sK9) = k4_lattices(sK7,sK10,sK9) ),
    inference(superposition,[status(thm)],[c_1324,c_3847])).

cnf(c_5205,plain,
    ( k2_lattices(sK7,sK10,sK9) = k4_lattices(sK7,sK9,sK10) ),
    inference(demodulation,[status(thm)],[c_5198,c_3954])).

cnf(c_7287,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_7282,c_5205])).

cnf(c_7291,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = sK10 ),
    inference(demodulation,[status(thm)],[c_7290,c_7287])).

cnf(c_1799,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK9,X0),k2_lattices(sK7,sK9,X1)) = k2_lattices(sK7,sK9,k1_lattices(sK7,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1316])).

cnf(c_6098,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,X0)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,X0))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1799])).

cnf(c_3848,plain,
    ( k2_lattices(sK7,sK9,X0) = k4_lattices(sK7,sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1320])).

cnf(c_4049,plain,
    ( k2_lattices(sK7,sK9,sK8) = k4_lattices(sK7,sK9,sK8) ),
    inference(superposition,[status(thm)],[c_1323,c_3848])).

cnf(c_6101,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,X0)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,X0))
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6098,c_4049])).

cnf(c_7562,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK10)) ),
    inference(superposition,[status(thm)],[c_1325,c_6101])).

cnf(c_4047,plain,
    ( k2_lattices(sK7,sK9,sK10) = k4_lattices(sK7,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1325,c_3848])).

cnf(c_7571,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_7562,c_3939,c_4047])).

cnf(c_7563,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,sK9)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK9)) ),
    inference(superposition,[status(thm)],[c_1324,c_6101])).

cnf(c_2693,plain,
    ( k1_lattices(sK7,sK9,sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_1324,c_1319])).

cnf(c_2083,plain,
    ( k2_lattices(sK7,sK9,k1_lattices(sK7,sK9,X0)) = sK9
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1318])).

cnf(c_2520,plain,
    ( k2_lattices(sK7,sK9,k1_lattices(sK7,sK9,sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_1324,c_2083])).

cnf(c_3319,plain,
    ( k2_lattices(sK7,sK9,sK9) = sK9 ),
    inference(demodulation,[status(thm)],[c_2693,c_2520])).

cnf(c_4519,plain,
    ( k2_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1324,c_3849])).

cnf(c_1986,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK9),sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_1324,c_1637])).

cnf(c_4892,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK8,sK9),sK9) = sK9 ),
    inference(demodulation,[status(thm)],[c_4519,c_1986])).

cnf(c_6948,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),sK9) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_4892,c_6000])).

cnf(c_7568,plain,
    ( k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK9)) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_7563,c_3319,c_6948])).

cnf(c_8565,plain,
    ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_7571,c_7568])).

cnf(c_8960,plain,
    ( sK10 = sK9 ),
    inference(light_normalisation,[status(thm)],[c_7291,c_8565])).

cnf(c_25,negated_conjecture,
    ( sK9 != sK10 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_9008,plain,
    ( sK9 != sK9 ),
    inference(demodulation,[status(thm)],[c_8960,c_25])).

cnf(c_9009,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9008])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.46/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/0.97  
% 3.46/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.97  
% 3.46/0.97  ------  iProver source info
% 3.46/0.97  
% 3.46/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.97  git: non_committed_changes: false
% 3.46/0.97  git: last_make_outside_of_git: false
% 3.46/0.97  
% 3.46/0.97  ------ 
% 3.46/0.97  
% 3.46/0.97  ------ Input Options
% 3.46/0.97  
% 3.46/0.97  --out_options                           all
% 3.46/0.97  --tptp_safe_out                         true
% 3.46/0.97  --problem_path                          ""
% 3.46/0.97  --include_path                          ""
% 3.46/0.97  --clausifier                            res/vclausify_rel
% 3.46/0.97  --clausifier_options                    --mode clausify
% 3.46/0.97  --stdin                                 false
% 3.46/0.97  --stats_out                             all
% 3.46/0.97  
% 3.46/0.97  ------ General Options
% 3.46/0.97  
% 3.46/0.97  --fof                                   false
% 3.46/0.97  --time_out_real                         305.
% 3.46/0.97  --time_out_virtual                      -1.
% 3.46/0.97  --symbol_type_check                     false
% 3.46/0.97  --clausify_out                          false
% 3.46/0.97  --sig_cnt_out                           false
% 3.46/0.97  --trig_cnt_out                          false
% 3.46/0.97  --trig_cnt_out_tolerance                1.
% 3.46/0.97  --trig_cnt_out_sk_spl                   false
% 3.46/0.97  --abstr_cl_out                          false
% 3.46/0.97  
% 3.46/0.97  ------ Global Options
% 3.46/0.97  
% 3.46/0.97  --schedule                              default
% 3.46/0.97  --add_important_lit                     false
% 3.46/0.97  --prop_solver_per_cl                    1000
% 3.46/0.97  --min_unsat_core                        false
% 3.46/0.97  --soft_assumptions                      false
% 3.46/0.97  --soft_lemma_size                       3
% 3.46/0.97  --prop_impl_unit_size                   0
% 3.46/0.97  --prop_impl_unit                        []
% 3.46/0.97  --share_sel_clauses                     true
% 3.46/0.97  --reset_solvers                         false
% 3.46/0.97  --bc_imp_inh                            [conj_cone]
% 3.46/0.97  --conj_cone_tolerance                   3.
% 3.46/0.97  --extra_neg_conj                        none
% 3.46/0.97  --large_theory_mode                     true
% 3.46/0.97  --prolific_symb_bound                   200
% 3.46/0.97  --lt_threshold                          2000
% 3.46/0.97  --clause_weak_htbl                      true
% 3.46/0.97  --gc_record_bc_elim                     false
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing Options
% 3.46/0.97  
% 3.46/0.97  --preprocessing_flag                    true
% 3.46/0.97  --time_out_prep_mult                    0.1
% 3.46/0.97  --splitting_mode                        input
% 3.46/0.97  --splitting_grd                         true
% 3.46/0.97  --splitting_cvd                         false
% 3.46/0.97  --splitting_cvd_svl                     false
% 3.46/0.97  --splitting_nvd                         32
% 3.46/0.97  --sub_typing                            true
% 3.46/0.97  --prep_gs_sim                           true
% 3.46/0.97  --prep_unflatten                        true
% 3.46/0.97  --prep_res_sim                          true
% 3.46/0.97  --prep_upred                            true
% 3.46/0.97  --prep_sem_filter                       exhaustive
% 3.46/0.97  --prep_sem_filter_out                   false
% 3.46/0.97  --pred_elim                             true
% 3.46/0.97  --res_sim_input                         true
% 3.46/0.97  --eq_ax_congr_red                       true
% 3.46/0.97  --pure_diseq_elim                       true
% 3.46/0.97  --brand_transform                       false
% 3.46/0.97  --non_eq_to_eq                          false
% 3.46/0.97  --prep_def_merge                        true
% 3.46/0.97  --prep_def_merge_prop_impl              false
% 3.46/0.97  --prep_def_merge_mbd                    true
% 3.46/0.97  --prep_def_merge_tr_red                 false
% 3.46/0.97  --prep_def_merge_tr_cl                  false
% 3.46/0.97  --smt_preprocessing                     true
% 3.46/0.97  --smt_ac_axioms                         fast
% 3.46/0.97  --preprocessed_out                      false
% 3.46/0.97  --preprocessed_stats                    false
% 3.46/0.97  
% 3.46/0.97  ------ Abstraction refinement Options
% 3.46/0.97  
% 3.46/0.97  --abstr_ref                             []
% 3.46/0.97  --abstr_ref_prep                        false
% 3.46/0.97  --abstr_ref_until_sat                   false
% 3.46/0.97  --abstr_ref_sig_restrict                funpre
% 3.46/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.97  --abstr_ref_under                       []
% 3.46/0.97  
% 3.46/0.97  ------ SAT Options
% 3.46/0.97  
% 3.46/0.97  --sat_mode                              false
% 3.46/0.97  --sat_fm_restart_options                ""
% 3.46/0.97  --sat_gr_def                            false
% 3.46/0.97  --sat_epr_types                         true
% 3.46/0.97  --sat_non_cyclic_types                  false
% 3.46/0.97  --sat_finite_models                     false
% 3.46/0.97  --sat_fm_lemmas                         false
% 3.46/0.97  --sat_fm_prep                           false
% 3.46/0.97  --sat_fm_uc_incr                        true
% 3.46/0.97  --sat_out_model                         small
% 3.46/0.97  --sat_out_clauses                       false
% 3.46/0.97  
% 3.46/0.97  ------ QBF Options
% 3.46/0.97  
% 3.46/0.97  --qbf_mode                              false
% 3.46/0.97  --qbf_elim_univ                         false
% 3.46/0.97  --qbf_dom_inst                          none
% 3.46/0.97  --qbf_dom_pre_inst                      false
% 3.46/0.97  --qbf_sk_in                             false
% 3.46/0.97  --qbf_pred_elim                         true
% 3.46/0.97  --qbf_split                             512
% 3.46/0.97  
% 3.46/0.97  ------ BMC1 Options
% 3.46/0.97  
% 3.46/0.97  --bmc1_incremental                      false
% 3.46/0.97  --bmc1_axioms                           reachable_all
% 3.46/0.97  --bmc1_min_bound                        0
% 3.46/0.97  --bmc1_max_bound                        -1
% 3.46/0.97  --bmc1_max_bound_default                -1
% 3.46/0.97  --bmc1_symbol_reachability              true
% 3.46/0.97  --bmc1_property_lemmas                  false
% 3.46/0.97  --bmc1_k_induction                      false
% 3.46/0.97  --bmc1_non_equiv_states                 false
% 3.46/0.97  --bmc1_deadlock                         false
% 3.46/0.97  --bmc1_ucm                              false
% 3.46/0.97  --bmc1_add_unsat_core                   none
% 3.46/0.97  --bmc1_unsat_core_children              false
% 3.46/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.97  --bmc1_out_stat                         full
% 3.46/0.97  --bmc1_ground_init                      false
% 3.46/0.97  --bmc1_pre_inst_next_state              false
% 3.46/0.97  --bmc1_pre_inst_state                   false
% 3.46/0.97  --bmc1_pre_inst_reach_state             false
% 3.46/0.97  --bmc1_out_unsat_core                   false
% 3.46/0.97  --bmc1_aig_witness_out                  false
% 3.46/0.97  --bmc1_verbose                          false
% 3.46/0.97  --bmc1_dump_clauses_tptp                false
% 3.46/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.97  --bmc1_dump_file                        -
% 3.46/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.97  --bmc1_ucm_extend_mode                  1
% 3.46/0.97  --bmc1_ucm_init_mode                    2
% 3.46/0.97  --bmc1_ucm_cone_mode                    none
% 3.46/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.97  --bmc1_ucm_relax_model                  4
% 3.46/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.97  --bmc1_ucm_layered_model                none
% 3.46/0.97  --bmc1_ucm_max_lemma_size               10
% 3.46/0.97  
% 3.46/0.97  ------ AIG Options
% 3.46/0.97  
% 3.46/0.97  --aig_mode                              false
% 3.46/0.97  
% 3.46/0.97  ------ Instantiation Options
% 3.46/0.97  
% 3.46/0.97  --instantiation_flag                    true
% 3.46/0.97  --inst_sos_flag                         false
% 3.46/0.97  --inst_sos_phase                        true
% 3.46/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel_side                     num_symb
% 3.46/0.97  --inst_solver_per_active                1400
% 3.46/0.97  --inst_solver_calls_frac                1.
% 3.46/0.97  --inst_passive_queue_type               priority_queues
% 3.46/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.97  --inst_passive_queues_freq              [25;2]
% 3.46/0.97  --inst_dismatching                      true
% 3.46/0.97  --inst_eager_unprocessed_to_passive     true
% 3.46/0.97  --inst_prop_sim_given                   true
% 3.46/0.97  --inst_prop_sim_new                     false
% 3.46/0.97  --inst_subs_new                         false
% 3.46/0.97  --inst_eq_res_simp                      false
% 3.46/0.97  --inst_subs_given                       false
% 3.46/0.97  --inst_orphan_elimination               true
% 3.46/0.97  --inst_learning_loop_flag               true
% 3.46/0.97  --inst_learning_start                   3000
% 3.46/0.97  --inst_learning_factor                  2
% 3.46/0.97  --inst_start_prop_sim_after_learn       3
% 3.46/0.97  --inst_sel_renew                        solver
% 3.46/0.97  --inst_lit_activity_flag                true
% 3.46/0.97  --inst_restr_to_given                   false
% 3.46/0.97  --inst_activity_threshold               500
% 3.46/0.97  --inst_out_proof                        true
% 3.46/0.97  
% 3.46/0.97  ------ Resolution Options
% 3.46/0.97  
% 3.46/0.97  --resolution_flag                       true
% 3.46/0.97  --res_lit_sel                           adaptive
% 3.46/0.97  --res_lit_sel_side                      none
% 3.46/0.97  --res_ordering                          kbo
% 3.46/0.97  --res_to_prop_solver                    active
% 3.46/0.97  --res_prop_simpl_new                    false
% 3.46/0.97  --res_prop_simpl_given                  true
% 3.46/0.97  --res_passive_queue_type                priority_queues
% 3.46/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.97  --res_passive_queues_freq               [15;5]
% 3.46/0.97  --res_forward_subs                      full
% 3.46/0.97  --res_backward_subs                     full
% 3.46/0.97  --res_forward_subs_resolution           true
% 3.46/0.97  --res_backward_subs_resolution          true
% 3.46/0.97  --res_orphan_elimination                true
% 3.46/0.97  --res_time_limit                        2.
% 3.46/0.97  --res_out_proof                         true
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Options
% 3.46/0.97  
% 3.46/0.97  --superposition_flag                    true
% 3.46/0.97  --sup_passive_queue_type                priority_queues
% 3.46/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.46/0.97  --demod_completeness_check              fast
% 3.46/0.97  --demod_use_ground                      true
% 3.46/0.97  --sup_to_prop_solver                    passive
% 3.46/0.97  --sup_prop_simpl_new                    true
% 3.46/0.97  --sup_prop_simpl_given                  true
% 3.46/0.97  --sup_fun_splitting                     false
% 3.46/0.97  --sup_smt_interval                      50000
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Simplification Setup
% 3.46/0.97  
% 3.46/0.97  --sup_indices_passive                   []
% 3.46/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_full_bw                           [BwDemod]
% 3.46/0.97  --sup_immed_triv                        [TrivRules]
% 3.46/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_immed_bw_main                     []
% 3.46/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.97  
% 3.46/0.97  ------ Combination Options
% 3.46/0.97  
% 3.46/0.97  --comb_res_mult                         3
% 3.46/0.97  --comb_sup_mult                         2
% 3.46/0.97  --comb_inst_mult                        10
% 3.46/0.97  
% 3.46/0.97  ------ Debug Options
% 3.46/0.97  
% 3.46/0.97  --dbg_backtrace                         false
% 3.46/0.97  --dbg_dump_prop_clauses                 false
% 3.46/0.97  --dbg_dump_prop_clauses_file            -
% 3.46/0.97  --dbg_out_stat                          false
% 3.46/0.97  ------ Parsing...
% 3.46/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.97  ------ Proving...
% 3.46/0.97  ------ Problem Properties 
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  clauses                                 14
% 3.46/0.97  conjectures                             6
% 3.46/0.97  EPR                                     1
% 3.46/0.97  Horn                                    14
% 3.46/0.97  unary                                   6
% 3.46/0.97  binary                                  2
% 3.46/0.97  lits                                    29
% 3.46/0.97  lits eq                                 12
% 3.46/0.97  fd_pure                                 0
% 3.46/0.97  fd_pseudo                               0
% 3.46/0.97  fd_cond                                 0
% 3.46/0.97  fd_pseudo_cond                          1
% 3.46/0.97  AC symbols                              0
% 3.46/0.97  
% 3.46/0.97  ------ Schedule dynamic 5 is on 
% 3.46/0.97  
% 3.46/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  ------ 
% 3.46/0.97  Current options:
% 3.46/0.97  ------ 
% 3.46/0.97  
% 3.46/0.97  ------ Input Options
% 3.46/0.97  
% 3.46/0.97  --out_options                           all
% 3.46/0.97  --tptp_safe_out                         true
% 3.46/0.97  --problem_path                          ""
% 3.46/0.97  --include_path                          ""
% 3.46/0.97  --clausifier                            res/vclausify_rel
% 3.46/0.97  --clausifier_options                    --mode clausify
% 3.46/0.97  --stdin                                 false
% 3.46/0.97  --stats_out                             all
% 3.46/0.97  
% 3.46/0.97  ------ General Options
% 3.46/0.97  
% 3.46/0.97  --fof                                   false
% 3.46/0.97  --time_out_real                         305.
% 3.46/0.97  --time_out_virtual                      -1.
% 3.46/0.97  --symbol_type_check                     false
% 3.46/0.97  --clausify_out                          false
% 3.46/0.97  --sig_cnt_out                           false
% 3.46/0.97  --trig_cnt_out                          false
% 3.46/0.97  --trig_cnt_out_tolerance                1.
% 3.46/0.97  --trig_cnt_out_sk_spl                   false
% 3.46/0.97  --abstr_cl_out                          false
% 3.46/0.97  
% 3.46/0.97  ------ Global Options
% 3.46/0.97  
% 3.46/0.97  --schedule                              default
% 3.46/0.97  --add_important_lit                     false
% 3.46/0.97  --prop_solver_per_cl                    1000
% 3.46/0.97  --min_unsat_core                        false
% 3.46/0.97  --soft_assumptions                      false
% 3.46/0.97  --soft_lemma_size                       3
% 3.46/0.97  --prop_impl_unit_size                   0
% 3.46/0.97  --prop_impl_unit                        []
% 3.46/0.97  --share_sel_clauses                     true
% 3.46/0.97  --reset_solvers                         false
% 3.46/0.97  --bc_imp_inh                            [conj_cone]
% 3.46/0.97  --conj_cone_tolerance                   3.
% 3.46/0.97  --extra_neg_conj                        none
% 3.46/0.97  --large_theory_mode                     true
% 3.46/0.97  --prolific_symb_bound                   200
% 3.46/0.97  --lt_threshold                          2000
% 3.46/0.97  --clause_weak_htbl                      true
% 3.46/0.97  --gc_record_bc_elim                     false
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing Options
% 3.46/0.97  
% 3.46/0.97  --preprocessing_flag                    true
% 3.46/0.97  --time_out_prep_mult                    0.1
% 3.46/0.97  --splitting_mode                        input
% 3.46/0.97  --splitting_grd                         true
% 3.46/0.97  --splitting_cvd                         false
% 3.46/0.97  --splitting_cvd_svl                     false
% 3.46/0.97  --splitting_nvd                         32
% 3.46/0.97  --sub_typing                            true
% 3.46/0.97  --prep_gs_sim                           true
% 3.46/0.97  --prep_unflatten                        true
% 3.46/0.97  --prep_res_sim                          true
% 3.46/0.97  --prep_upred                            true
% 3.46/0.97  --prep_sem_filter                       exhaustive
% 3.46/0.97  --prep_sem_filter_out                   false
% 3.46/0.97  --pred_elim                             true
% 3.46/0.97  --res_sim_input                         true
% 3.46/0.97  --eq_ax_congr_red                       true
% 3.46/0.97  --pure_diseq_elim                       true
% 3.46/0.97  --brand_transform                       false
% 3.46/0.97  --non_eq_to_eq                          false
% 3.46/0.97  --prep_def_merge                        true
% 3.46/0.97  --prep_def_merge_prop_impl              false
% 3.46/0.97  --prep_def_merge_mbd                    true
% 3.46/0.97  --prep_def_merge_tr_red                 false
% 3.46/0.97  --prep_def_merge_tr_cl                  false
% 3.46/0.97  --smt_preprocessing                     true
% 3.46/0.97  --smt_ac_axioms                         fast
% 3.46/0.97  --preprocessed_out                      false
% 3.46/0.97  --preprocessed_stats                    false
% 3.46/0.97  
% 3.46/0.97  ------ Abstraction refinement Options
% 3.46/0.97  
% 3.46/0.97  --abstr_ref                             []
% 3.46/0.97  --abstr_ref_prep                        false
% 3.46/0.97  --abstr_ref_until_sat                   false
% 3.46/0.97  --abstr_ref_sig_restrict                funpre
% 3.46/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.97  --abstr_ref_under                       []
% 3.46/0.97  
% 3.46/0.97  ------ SAT Options
% 3.46/0.97  
% 3.46/0.97  --sat_mode                              false
% 3.46/0.97  --sat_fm_restart_options                ""
% 3.46/0.97  --sat_gr_def                            false
% 3.46/0.97  --sat_epr_types                         true
% 3.46/0.97  --sat_non_cyclic_types                  false
% 3.46/0.97  --sat_finite_models                     false
% 3.46/0.97  --sat_fm_lemmas                         false
% 3.46/0.97  --sat_fm_prep                           false
% 3.46/0.97  --sat_fm_uc_incr                        true
% 3.46/0.97  --sat_out_model                         small
% 3.46/0.97  --sat_out_clauses                       false
% 3.46/0.97  
% 3.46/0.97  ------ QBF Options
% 3.46/0.97  
% 3.46/0.97  --qbf_mode                              false
% 3.46/0.97  --qbf_elim_univ                         false
% 3.46/0.97  --qbf_dom_inst                          none
% 3.46/0.97  --qbf_dom_pre_inst                      false
% 3.46/0.97  --qbf_sk_in                             false
% 3.46/0.97  --qbf_pred_elim                         true
% 3.46/0.97  --qbf_split                             512
% 3.46/0.97  
% 3.46/0.97  ------ BMC1 Options
% 3.46/0.97  
% 3.46/0.97  --bmc1_incremental                      false
% 3.46/0.97  --bmc1_axioms                           reachable_all
% 3.46/0.97  --bmc1_min_bound                        0
% 3.46/0.97  --bmc1_max_bound                        -1
% 3.46/0.97  --bmc1_max_bound_default                -1
% 3.46/0.97  --bmc1_symbol_reachability              true
% 3.46/0.97  --bmc1_property_lemmas                  false
% 3.46/0.97  --bmc1_k_induction                      false
% 3.46/0.97  --bmc1_non_equiv_states                 false
% 3.46/0.97  --bmc1_deadlock                         false
% 3.46/0.97  --bmc1_ucm                              false
% 3.46/0.97  --bmc1_add_unsat_core                   none
% 3.46/0.97  --bmc1_unsat_core_children              false
% 3.46/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.97  --bmc1_out_stat                         full
% 3.46/0.97  --bmc1_ground_init                      false
% 3.46/0.97  --bmc1_pre_inst_next_state              false
% 3.46/0.97  --bmc1_pre_inst_state                   false
% 3.46/0.97  --bmc1_pre_inst_reach_state             false
% 3.46/0.97  --bmc1_out_unsat_core                   false
% 3.46/0.97  --bmc1_aig_witness_out                  false
% 3.46/0.97  --bmc1_verbose                          false
% 3.46/0.97  --bmc1_dump_clauses_tptp                false
% 3.46/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.97  --bmc1_dump_file                        -
% 3.46/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.97  --bmc1_ucm_extend_mode                  1
% 3.46/0.97  --bmc1_ucm_init_mode                    2
% 3.46/0.97  --bmc1_ucm_cone_mode                    none
% 3.46/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.97  --bmc1_ucm_relax_model                  4
% 3.46/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.97  --bmc1_ucm_layered_model                none
% 3.46/0.97  --bmc1_ucm_max_lemma_size               10
% 3.46/0.97  
% 3.46/0.97  ------ AIG Options
% 3.46/0.97  
% 3.46/0.97  --aig_mode                              false
% 3.46/0.97  
% 3.46/0.97  ------ Instantiation Options
% 3.46/0.97  
% 3.46/0.97  --instantiation_flag                    true
% 3.46/0.97  --inst_sos_flag                         false
% 3.46/0.97  --inst_sos_phase                        true
% 3.46/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel_side                     none
% 3.46/0.97  --inst_solver_per_active                1400
% 3.46/0.97  --inst_solver_calls_frac                1.
% 3.46/0.97  --inst_passive_queue_type               priority_queues
% 3.46/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.97  --inst_passive_queues_freq              [25;2]
% 3.46/0.97  --inst_dismatching                      true
% 3.46/0.97  --inst_eager_unprocessed_to_passive     true
% 3.46/0.97  --inst_prop_sim_given                   true
% 3.46/0.97  --inst_prop_sim_new                     false
% 3.46/0.97  --inst_subs_new                         false
% 3.46/0.97  --inst_eq_res_simp                      false
% 3.46/0.97  --inst_subs_given                       false
% 3.46/0.97  --inst_orphan_elimination               true
% 3.46/0.97  --inst_learning_loop_flag               true
% 3.46/0.97  --inst_learning_start                   3000
% 3.46/0.97  --inst_learning_factor                  2
% 3.46/0.97  --inst_start_prop_sim_after_learn       3
% 3.46/0.97  --inst_sel_renew                        solver
% 3.46/0.97  --inst_lit_activity_flag                true
% 3.46/0.97  --inst_restr_to_given                   false
% 3.46/0.97  --inst_activity_threshold               500
% 3.46/0.97  --inst_out_proof                        true
% 3.46/0.97  
% 3.46/0.97  ------ Resolution Options
% 3.46/0.97  
% 3.46/0.97  --resolution_flag                       false
% 3.46/0.97  --res_lit_sel                           adaptive
% 3.46/0.97  --res_lit_sel_side                      none
% 3.46/0.97  --res_ordering                          kbo
% 3.46/0.97  --res_to_prop_solver                    active
% 3.46/0.97  --res_prop_simpl_new                    false
% 3.46/0.97  --res_prop_simpl_given                  true
% 3.46/0.97  --res_passive_queue_type                priority_queues
% 3.46/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.97  --res_passive_queues_freq               [15;5]
% 3.46/0.97  --res_forward_subs                      full
% 3.46/0.97  --res_backward_subs                     full
% 3.46/0.97  --res_forward_subs_resolution           true
% 3.46/0.97  --res_backward_subs_resolution          true
% 3.46/0.97  --res_orphan_elimination                true
% 3.46/0.97  --res_time_limit                        2.
% 3.46/0.97  --res_out_proof                         true
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Options
% 3.46/0.97  
% 3.46/0.97  --superposition_flag                    true
% 3.46/0.97  --sup_passive_queue_type                priority_queues
% 3.46/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.46/0.98  --demod_completeness_check              fast
% 3.46/0.98  --demod_use_ground                      true
% 3.46/0.98  --sup_to_prop_solver                    passive
% 3.46/0.98  --sup_prop_simpl_new                    true
% 3.46/0.98  --sup_prop_simpl_given                  true
% 3.46/0.98  --sup_fun_splitting                     false
% 3.46/0.98  --sup_smt_interval                      50000
% 3.46/0.98  
% 3.46/0.98  ------ Superposition Simplification Setup
% 3.46/0.98  
% 3.46/0.98  --sup_indices_passive                   []
% 3.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.98  --sup_full_bw                           [BwDemod]
% 3.46/0.98  --sup_immed_triv                        [TrivRules]
% 3.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.98  --sup_immed_bw_main                     []
% 3.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.98  
% 3.46/0.98  ------ Combination Options
% 3.46/0.98  
% 3.46/0.98  --comb_res_mult                         3
% 3.46/0.98  --comb_sup_mult                         2
% 3.46/0.98  --comb_inst_mult                        10
% 3.46/0.98  
% 3.46/0.98  ------ Debug Options
% 3.46/0.98  
% 3.46/0.98  --dbg_backtrace                         false
% 3.46/0.98  --dbg_dump_prop_clauses                 false
% 3.46/0.98  --dbg_dump_prop_clauses_file            -
% 3.46/0.98  --dbg_out_stat                          false
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  ------ Proving...
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  % SZS status Theorem for theBenchmark.p
% 3.46/0.98  
% 3.46/0.98   Resolution empty clause
% 3.46/0.98  
% 3.46/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/0.98  
% 3.46/0.98  fof(f11,conjecture,(
% 3.46/0.98    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f12,negated_conjecture,(
% 3.46/0.98    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.46/0.98    inference(negated_conjecture,[],[f11])).
% 3.46/0.98  
% 3.46/0.98  fof(f33,plain,(
% 3.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f12])).
% 3.46/0.98  
% 3.46/0.98  fof(f34,plain,(
% 3.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f33])).
% 3.46/0.98  
% 3.46/0.98  fof(f54,plain,(
% 3.46/0.98    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK10 != X2 & k3_lattices(X0,X1,sK10) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK10) = k4_lattices(X0,X1,X2) & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f53,plain,(
% 3.46/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK9 != X3 & k3_lattices(X0,X1,sK9) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK9) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f52,plain,(
% 3.46/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK8,X2) = k3_lattices(X0,sK8,X3) & k4_lattices(X0,sK8,X2) = k4_lattices(X0,sK8,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f51,plain,(
% 3.46/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK7,X1,X2) = k3_lattices(sK7,X1,X3) & k4_lattices(sK7,X1,X2) = k4_lattices(sK7,X1,X3) & m1_subset_1(X3,u1_struct_0(sK7))) & m1_subset_1(X2,u1_struct_0(sK7))) & m1_subset_1(X1,u1_struct_0(sK7))) & l3_lattices(sK7) & v11_lattices(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7))),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f55,plain,(
% 3.46/0.98    (((sK9 != sK10 & k3_lattices(sK7,sK8,sK9) = k3_lattices(sK7,sK8,sK10) & k4_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK10) & m1_subset_1(sK10,u1_struct_0(sK7))) & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK7))) & l3_lattices(sK7) & v11_lattices(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7)),
% 3.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f34,f54,f53,f52,f51])).
% 3.46/0.98  
% 3.46/0.98  fof(f87,plain,(
% 3.46/0.98    m1_subset_1(sK10,u1_struct_0(sK7))),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f85,plain,(
% 3.46/0.98    m1_subset_1(sK8,u1_struct_0(sK7))),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f4,axiom,(
% 3.46/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)))))))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f20,plain,(
% 3.46/0.98    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f4])).
% 3.46/0.98  
% 3.46/0.98  fof(f21,plain,(
% 3.46/0.98    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f20])).
% 3.46/0.98  
% 3.46/0.98  fof(f35,plain,(
% 3.46/0.98    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(nnf_transformation,[],[f21])).
% 3.46/0.98  
% 3.46/0.98  fof(f36,plain,(
% 3.46/0.98    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(rectify,[],[f35])).
% 3.46/0.98  
% 3.46/0.98  fof(f39,plain,(
% 3.46/0.98    ( ! [X2,X1] : (! [X0] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f38,plain,(
% 3.46/0.98    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f37,plain,(
% 3.46/0.98    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f40,plain,(
% 3.46/0.98    ! [X0] : (((v11_lattices(X0) | (((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 3.46/0.98  
% 3.46/0.98  fof(f63,plain,(
% 3.46/0.98    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f40])).
% 3.46/0.98  
% 3.46/0.98  fof(f81,plain,(
% 3.46/0.98    ~v2_struct_0(sK7)),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f84,plain,(
% 3.46/0.98    l3_lattices(sK7)),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f83,plain,(
% 3.46/0.98    v11_lattices(sK7)),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f7,axiom,(
% 3.46/0.98    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f26,plain,(
% 3.46/0.98    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.46/0.98    inference(ennf_transformation,[],[f7])).
% 3.46/0.98  
% 3.46/0.98  fof(f76,plain,(
% 3.46/0.98    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f26])).
% 3.46/0.98  
% 3.46/0.98  fof(f9,axiom,(
% 3.46/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f29,plain,(
% 3.46/0.98    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f9])).
% 3.46/0.98  
% 3.46/0.98  fof(f30,plain,(
% 3.46/0.98    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f29])).
% 3.46/0.98  
% 3.46/0.98  fof(f79,plain,(
% 3.46/0.98    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f30])).
% 3.46/0.98  
% 3.46/0.98  fof(f2,axiom,(
% 3.46/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f13,plain,(
% 3.46/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.46/0.98    inference(pure_predicate_removal,[],[f2])).
% 3.46/0.98  
% 3.46/0.98  fof(f14,plain,(
% 3.46/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.46/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.46/0.98  
% 3.46/0.98  fof(f16,plain,(
% 3.46/0.98    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.46/0.98    inference(ennf_transformation,[],[f14])).
% 3.46/0.98  
% 3.46/0.98  fof(f17,plain,(
% 3.46/0.98    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.46/0.98    inference(flattening,[],[f16])).
% 3.46/0.98  
% 3.46/0.98  fof(f59,plain,(
% 3.46/0.98    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f17])).
% 3.46/0.98  
% 3.46/0.98  fof(f82,plain,(
% 3.46/0.98    v10_lattices(sK7)),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f86,plain,(
% 3.46/0.98    m1_subset_1(sK9,u1_struct_0(sK7))),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f3,axiom,(
% 3.46/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f18,plain,(
% 3.46/0.98    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f3])).
% 3.46/0.98  
% 3.46/0.98  fof(f19,plain,(
% 3.46/0.98    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f18])).
% 3.46/0.98  
% 3.46/0.98  fof(f62,plain,(
% 3.46/0.98    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f19])).
% 3.46/0.98  
% 3.46/0.98  fof(f88,plain,(
% 3.46/0.98    k4_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK10)),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f10,axiom,(
% 3.46/0.98    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f31,plain,(
% 3.46/0.98    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f10])).
% 3.46/0.98  
% 3.46/0.98  fof(f32,plain,(
% 3.46/0.98    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f31])).
% 3.46/0.98  
% 3.46/0.98  fof(f80,plain,(
% 3.46/0.98    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f32])).
% 3.46/0.98  
% 3.46/0.98  fof(f60,plain,(
% 3.46/0.98    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f17])).
% 3.46/0.98  
% 3.46/0.98  fof(f61,plain,(
% 3.46/0.98    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f17])).
% 3.46/0.98  
% 3.46/0.98  fof(f6,axiom,(
% 3.46/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f24,plain,(
% 3.46/0.98    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f6])).
% 3.46/0.98  
% 3.46/0.98  fof(f25,plain,(
% 3.46/0.98    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f24])).
% 3.46/0.98  
% 3.46/0.98  fof(f46,plain,(
% 3.46/0.98    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(nnf_transformation,[],[f25])).
% 3.46/0.98  
% 3.46/0.98  fof(f47,plain,(
% 3.46/0.98    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(rectify,[],[f46])).
% 3.46/0.98  
% 3.46/0.98  fof(f49,plain,(
% 3.46/0.98    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK6(X0))) != X1 & m1_subset_1(sK6(X0),u1_struct_0(X0))))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f48,plain,(
% 3.46/0.98    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) != sK5(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f50,plain,(
% 3.46/0.98    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != sK5(X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f47,f49,f48])).
% 3.46/0.98  
% 3.46/0.98  fof(f72,plain,(
% 3.46/0.98    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f50])).
% 3.46/0.98  
% 3.46/0.98  fof(f58,plain,(
% 3.46/0.98    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f17])).
% 3.46/0.98  
% 3.46/0.98  fof(f77,plain,(
% 3.46/0.98    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f26])).
% 3.46/0.98  
% 3.46/0.98  fof(f8,axiom,(
% 3.46/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f27,plain,(
% 3.46/0.98    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f8])).
% 3.46/0.98  
% 3.46/0.98  fof(f28,plain,(
% 3.46/0.98    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f27])).
% 3.46/0.98  
% 3.46/0.98  fof(f78,plain,(
% 3.46/0.98    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f28])).
% 3.46/0.98  
% 3.46/0.98  fof(f89,plain,(
% 3.46/0.98    k3_lattices(sK7,sK8,sK9) = k3_lattices(sK7,sK8,sK10)),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  fof(f5,axiom,(
% 3.46/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 3.46/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.98  
% 3.46/0.98  fof(f22,plain,(
% 3.46/0.98    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.46/0.98    inference(ennf_transformation,[],[f5])).
% 3.46/0.98  
% 3.46/0.98  fof(f23,plain,(
% 3.46/0.98    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(flattening,[],[f22])).
% 3.46/0.98  
% 3.46/0.98  fof(f41,plain,(
% 3.46/0.98    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(nnf_transformation,[],[f23])).
% 3.46/0.98  
% 3.46/0.98  fof(f42,plain,(
% 3.46/0.98    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(rectify,[],[f41])).
% 3.46/0.98  
% 3.46/0.98  fof(f44,plain,(
% 3.46/0.98    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f43,plain,(
% 3.46/0.98    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.46/0.98    introduced(choice_axiom,[])).
% 3.46/0.98  
% 3.46/0.98  fof(f45,plain,(
% 3.46/0.98    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 3.46/0.98  
% 3.46/0.98  fof(f68,plain,(
% 3.46/0.98    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.46/0.98    inference(cnf_transformation,[],[f45])).
% 3.46/0.98  
% 3.46/0.98  fof(f90,plain,(
% 3.46/0.98    sK9 != sK10),
% 3.46/0.98    inference(cnf_transformation,[],[f55])).
% 3.46/0.98  
% 3.46/0.98  cnf(c_28,negated_conjecture,
% 3.46/0.98      ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 3.46/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1325,plain,
% 3.46/0.98      ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_30,negated_conjecture,
% 3.46/0.98      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 3.46/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1323,plain,
% 3.46/0.98      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_11,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.46/0.98      | ~ v11_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
% 3.46/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_34,negated_conjecture,
% 3.46/0.98      ( ~ v2_struct_0(sK7) ),
% 3.46/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1041,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.46/0.98      | ~ v11_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_34]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1042,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.46/0.98      | ~ v11_lattices(sK7)
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X2,X0),k2_lattices(sK7,X2,X1)) = k2_lattices(sK7,X2,k1_lattices(sK7,X0,X1)) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_1041]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_31,negated_conjecture,
% 3.46/0.98      ( l3_lattices(sK7) ),
% 3.46/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_32,negated_conjecture,
% 3.46/0.98      ( v11_lattices(sK7) ),
% 3.46/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_927,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_32]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_928,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X2,X0),k2_lattices(sK7,X2,X1)) = k2_lattices(sK7,X2,k1_lattices(sK7,X0,X1)) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_927]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1044,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X2,X0),k2_lattices(sK7,X2,X1)) = k2_lattices(sK7,X2,k1_lattices(sK7,X0,X1)) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_1042,c_34,c_31,c_928]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1045,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),k2_lattices(sK7,X0,X2)) = k2_lattices(sK7,X0,k1_lattices(sK7,X1,X2)) ),
% 3.46/0.98      inference(renaming,[status(thm)],[c_1044]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1316,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,X0,X1),k2_lattices(sK7,X0,X2)) = k2_lattices(sK7,X0,k1_lattices(sK7,X1,X2))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1045]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1798,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK10,X0),k2_lattices(sK7,sK10,X1)) = k2_lattices(sK7,sK10,k1_lattices(sK7,X0,X1))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_1316]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6009,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK10,sK8),k2_lattices(sK7,sK10,X0)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,X0))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_1798]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_21,plain,
% 3.46/0.98      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_23,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l1_lattices(X1)
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_394,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X3)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | X1 != X3
% 3.46/0.98      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_395,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_394]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3,plain,
% 3.46/0.98      ( v6_lattices(X0)
% 3.46/0.98      | ~ l3_lattices(X0)
% 3.46/0.98      | v2_struct_0(X0)
% 3.46/0.98      | ~ v10_lattices(X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_33,negated_conjecture,
% 3.46/0.98      ( v10_lattices(sK7) ),
% 3.46/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_456,plain,
% 3.46/0.98      ( v6_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK7 != X0 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_33]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_457,plain,
% 3.46/0.98      ( v6_lattices(sK7) | ~ l3_lattices(sK7) | v2_struct_0(sK7) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_456]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_96,plain,
% 3.46/0.98      ( v6_lattices(sK7)
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | ~ v10_lattices(sK7) ),
% 3.46/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_459,plain,
% 3.46/0.98      ( v6_lattices(sK7) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_457,c_34,c_33,c_31,c_96]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_541,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_395,c_459]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_542,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | k2_lattices(sK7,X0,X1) = k4_lattices(sK7,X0,X1) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_541]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_546,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | k2_lattices(sK7,X0,X1) = k4_lattices(sK7,X0,X1) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_542,c_34,c_31]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1320,plain,
% 3.46/0.98      ( k2_lattices(sK7,X0,X1) = k4_lattices(sK7,X0,X1)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3847,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,X0) = k4_lattices(sK7,sK10,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_1320]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3955,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,sK8) = k4_lattices(sK7,sK10,sK8) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_3847]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6012,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK10,sK8),k2_lattices(sK7,sK10,X0)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,X0))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_6009,c_3955]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_29,negated_conjecture,
% 3.46/0.98      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.46/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1324,plain,
% 3.46/0.98      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l1_lattices(X1)
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_418,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X3)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | X1 != X3
% 3.46/0.98      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_6]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_419,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_418]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_520,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_419,c_459]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_521,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | k4_lattices(sK7,X0,X1) = k4_lattices(sK7,X1,X0) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_520]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_525,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | k4_lattices(sK7,X0,X1) = k4_lattices(sK7,X1,X0) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_521,c_34,c_31]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1321,plain,
% 3.46/0.98      ( k4_lattices(sK7,X0,X1) = k4_lattices(sK7,X1,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4156,plain,
% 3.46/0.98      ( k4_lattices(sK7,X0,sK9) = k4_lattices(sK7,sK9,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_1321]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6000,plain,
% 3.46/0.98      ( k4_lattices(sK7,sK9,sK8) = k4_lattices(sK7,sK8,sK9) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_4156]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4155,plain,
% 3.46/0.98      ( k4_lattices(sK7,X0,sK10) = k4_lattices(sK7,sK10,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_1321]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_5199,plain,
% 3.46/0.98      ( k4_lattices(sK7,sK10,sK8) = k4_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_4155]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_27,negated_conjecture,
% 3.46/0.98      ( k4_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_5590,plain,
% 3.46/0.98      ( k4_lattices(sK7,sK10,sK8) = k4_lattices(sK7,sK8,sK9) ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_5199,c_27]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6034,plain,
% 3.46/0.98      ( k4_lattices(sK7,sK9,sK8) = k4_lattices(sK7,sK10,sK8) ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_6000,c_5590]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7275,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK10,X0)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,X0))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_6012,c_6034]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7281,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK10,sK10)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK10)) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_7275]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_24,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ v6_lattices(X1)
% 3.46/0.98      | ~ v8_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | ~ v9_lattices(X1)
% 3.46/0.98      | k1_lattices(X1,X0,X0) = X0 ),
% 3.46/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_562,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ v8_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | ~ v9_lattices(X1)
% 3.46/0.98      | k1_lattices(X1,X0,X0) = X0
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_459]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_563,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ v8_lattices(sK7)
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | ~ v9_lattices(sK7)
% 3.46/0.98      | k1_lattices(sK7,X0,X0) = X0 ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_562]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2,plain,
% 3.46/0.98      ( v8_lattices(X0)
% 3.46/0.98      | ~ l3_lattices(X0)
% 3.46/0.98      | v2_struct_0(X0)
% 3.46/0.98      | ~ v10_lattices(X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_99,plain,
% 3.46/0.98      ( v8_lattices(sK7)
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | ~ v10_lattices(sK7) ),
% 3.46/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1,plain,
% 3.46/0.98      ( ~ l3_lattices(X0)
% 3.46/0.98      | v2_struct_0(X0)
% 3.46/0.98      | ~ v10_lattices(X0)
% 3.46/0.98      | v9_lattices(X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_102,plain,
% 3.46/0.98      ( ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | ~ v10_lattices(sK7)
% 3.46/0.98      | v9_lattices(sK7) ),
% 3.46/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_567,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7)) | k1_lattices(sK7,X0,X0) = X0 ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_563,c_34,c_33,c_31,c_99,c_102]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1319,plain,
% 3.46/0.98      ( k1_lattices(sK7,X0,X0) = X0
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2692,plain,
% 3.46/0.98      ( k1_lattices(sK7,sK10,sK10) = sK10 ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_1319]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_19,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | ~ v9_lattices(X1)
% 3.46/0.98      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 3.46/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1003,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | ~ v9_lattices(X1)
% 3.46/0.98      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1004,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | ~ v9_lattices(sK7)
% 3.46/0.98      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_1003]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_478,plain,
% 3.46/0.98      ( ~ l3_lattices(X0) | v2_struct_0(X0) | v9_lattices(X0) | sK7 != X0 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_33]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_479,plain,
% 3.46/0.98      ( ~ l3_lattices(sK7) | v2_struct_0(sK7) | v9_lattices(sK7) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_478]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_481,plain,
% 3.46/0.98      ( v9_lattices(sK7) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_479,c_34,c_33,c_31,c_102]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_663,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_481]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_664,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_663]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1008,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_1004,c_34,c_31,c_664]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1318,plain,
% 3.46/0.98      ( k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2082,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,k1_lattices(sK7,sK10,X0)) = sK10
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_1318]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2214,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,k1_lattices(sK7,sK10,sK10)) = sK10 ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_2082]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3317,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,sK10) = sK10 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_2692,c_2214]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4,plain,
% 3.46/0.98      ( v4_lattices(X0)
% 3.46/0.98      | ~ l3_lattices(X0)
% 3.46/0.98      | v2_struct_0(X0)
% 3.46/0.98      | ~ v10_lattices(X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_20,plain,
% 3.46/0.98      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_22,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l2_lattices(X1)
% 3.46/0.98      | ~ v4_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_332,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v4_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X3)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | X1 != X3
% 3.46/0.98      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_333,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v4_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_332]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_363,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X3)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X3)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | ~ v10_lattices(X3)
% 3.46/0.98      | X1 != X3
% 3.46/0.98      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_333]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_364,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | ~ v10_lattices(X1)
% 3.46/0.98      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_363]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_489,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_33,c_364]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_490,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | k3_lattices(sK7,X1,X0) = k1_lattices(sK7,X1,X0) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_489]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_494,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | k3_lattices(sK7,X1,X0) = k1_lattices(sK7,X1,X0) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_490,c_34,c_31]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1322,plain,
% 3.46/0.98      ( k3_lattices(sK7,X0,X1) = k1_lattices(sK7,X0,X1)
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3559,plain,
% 3.46/0.98      ( k3_lattices(sK7,sK8,X0) = k1_lattices(sK7,sK8,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_1322]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3834,plain,
% 3.46/0.98      ( k3_lattices(sK7,sK8,sK9) = k1_lattices(sK7,sK8,sK9) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_3559]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3833,plain,
% 3.46/0.98      ( k3_lattices(sK7,sK8,sK10) = k1_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_3559]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_26,negated_conjecture,
% 3.46/0.98      ( k3_lattices(sK7,sK8,sK9) = k3_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3872,plain,
% 3.46/0.98      ( k3_lattices(sK7,sK8,sK9) = k1_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_3833,c_26]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3939,plain,
% 3.46/0.98      ( k1_lattices(sK7,sK8,sK9) = k1_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_3834,c_3872]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3849,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK8,X0) = k4_lattices(sK7,sK8,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_1320]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4518,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK8,sK10) = k4_lattices(sK7,sK8,sK10) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_3849]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4527,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK8,sK10) = k4_lattices(sK7,sK8,sK9) ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_4518,c_27]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_15,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v8_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 3.46/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1022,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ v8_lattices(X1)
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1023,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ v8_lattices(sK7)
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_1022]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_467,plain,
% 3.46/0.98      ( v8_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK7 != X0 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_33]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_468,plain,
% 3.46/0.98      ( v8_lattices(sK7) | ~ l3_lattices(sK7) | v2_struct_0(sK7) ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_467]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_470,plain,
% 3.46/0.98      ( v8_lattices(sK7) ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_468,c_34,c_33,c_31,c_99]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_777,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.46/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.46/0.98      | ~ l3_lattices(X1)
% 3.46/0.98      | v2_struct_0(X1)
% 3.46/0.98      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.46/0.98      | sK7 != X1 ),
% 3.46/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_470]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_778,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | ~ l3_lattices(sK7)
% 3.46/0.98      | v2_struct_0(sK7)
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 3.46/0.98      inference(unflattening,[status(thm)],[c_777]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1027,plain,
% 3.46/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.46/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.46/0.98      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 3.46/0.98      inference(global_propositional_subsumption,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_1023,c_34,c_31,c_778]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1317,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1027]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1637,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK8,X0),X0) = X0
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_1317]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1985,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),sK10) = sK10 ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_1637]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4530,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK8,sK9),sK10) = sK10 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_4527,c_1985]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_5592,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK10,sK8),sK10) = sK10 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_5590,c_4530]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6058,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),sK10) = sK10 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_6034,c_5592]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7290,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK9)) = sK10 ),
% 3.46/0.98      inference(light_normalisation,
% 3.46/0.98                [status(thm)],
% 3.46/0.98                [c_7281,c_3317,c_3939,c_6058]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7282,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK10,sK9)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK9)) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_7275]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_5198,plain,
% 3.46/0.98      ( k4_lattices(sK7,sK9,sK10) = k4_lattices(sK7,sK10,sK9) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_4155]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3954,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,sK9) = k4_lattices(sK7,sK10,sK9) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_3847]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_5205,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK10,sK9) = k4_lattices(sK7,sK9,sK10) ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_5198,c_3954]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7287,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK10,k1_lattices(sK7,sK8,sK9)) ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_7282,c_5205]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7291,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = sK10 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_7290,c_7287]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1799,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK9,X0),k2_lattices(sK7,sK9,X1)) = k2_lattices(sK7,sK9,k1_lattices(sK7,X0,X1))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.46/0.98      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_1316]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6098,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,X0)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,X0))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_1799]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3848,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,X0) = k4_lattices(sK7,sK9,X0)
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_1320]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4049,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,sK8) = k4_lattices(sK7,sK9,sK8) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1323,c_3848]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6101,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,X0)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,X0))
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_6098,c_4049]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7562,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK10)) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_6101]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4047,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,sK10) = k4_lattices(sK7,sK9,sK10) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1325,c_3848]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7571,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK9)) ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_7562,c_3939,c_4047]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7563,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k2_lattices(sK7,sK9,sK9)) = k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK9)) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_6101]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2693,plain,
% 3.46/0.98      ( k1_lattices(sK7,sK9,sK9) = sK9 ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_1319]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2083,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,k1_lattices(sK7,sK9,X0)) = sK9
% 3.46/0.98      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_1318]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_2520,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,k1_lattices(sK7,sK9,sK9)) = sK9 ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_2083]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_3319,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,sK9) = sK9 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_2693,c_2520]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4519,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK8,sK9) = k4_lattices(sK7,sK8,sK9) ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_3849]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_1986,plain,
% 3.46/0.98      ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK9),sK9) = sK9 ),
% 3.46/0.98      inference(superposition,[status(thm)],[c_1324,c_1637]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_4892,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK8,sK9),sK9) = sK9 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_4519,c_1986]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_6948,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),sK9) = sK9 ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_4892,c_6000]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_7568,plain,
% 3.46/0.98      ( k2_lattices(sK7,sK9,k1_lattices(sK7,sK8,sK9)) = sK9 ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_7563,c_3319,c_6948]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_8565,plain,
% 3.46/0.98      ( k1_lattices(sK7,k4_lattices(sK7,sK9,sK8),k4_lattices(sK7,sK9,sK10)) = sK9 ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_7571,c_7568]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_8960,plain,
% 3.46/0.98      ( sK10 = sK9 ),
% 3.46/0.98      inference(light_normalisation,[status(thm)],[c_7291,c_8565]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_25,negated_conjecture,
% 3.46/0.98      ( sK9 != sK10 ),
% 3.46/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_9008,plain,
% 3.46/0.98      ( sK9 != sK9 ),
% 3.46/0.98      inference(demodulation,[status(thm)],[c_8960,c_25]) ).
% 3.46/0.98  
% 3.46/0.98  cnf(c_9009,plain,
% 3.46/0.98      ( $false ),
% 3.46/0.98      inference(equality_resolution_simp,[status(thm)],[c_9008]) ).
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/0.98  
% 3.46/0.98  ------                               Statistics
% 3.46/0.98  
% 3.46/0.98  ------ General
% 3.46/0.98  
% 3.46/0.98  abstr_ref_over_cycles:                  0
% 3.46/0.98  abstr_ref_under_cycles:                 0
% 3.46/0.98  gc_basic_clause_elim:                   0
% 3.46/0.98  forced_gc_time:                         0
% 3.46/0.98  parsing_time:                           0.024
% 3.46/0.98  unif_index_cands_time:                  0.
% 3.46/0.98  unif_index_add_time:                    0.
% 3.46/0.98  orderings_time:                         0.
% 3.46/0.98  out_proof_time:                         0.017
% 3.46/0.98  total_time:                             0.332
% 3.46/0.98  num_of_symbols:                         59
% 3.46/0.98  num_of_terms:                           8020
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing
% 3.46/0.98  
% 3.46/0.98  num_of_splits:                          0
% 3.46/0.98  num_of_split_atoms:                     0
% 3.46/0.98  num_of_reused_defs:                     0
% 3.46/0.98  num_eq_ax_congr_red:                    23
% 3.46/0.98  num_of_sem_filtered_clauses:            1
% 3.46/0.98  num_of_subtypes:                        0
% 3.46/0.98  monotx_restored_types:                  0
% 3.46/0.98  sat_num_of_epr_types:                   0
% 3.46/0.98  sat_num_of_non_cyclic_types:            0
% 3.46/0.98  sat_guarded_non_collapsed_types:        0
% 3.46/0.98  num_pure_diseq_elim:                    0
% 3.46/0.98  simp_replaced_by:                       0
% 3.46/0.98  res_preprocessed:                       93
% 3.46/0.98  prep_upred:                             0
% 3.46/0.98  prep_unflattend:                        37
% 3.46/0.98  smt_new_axioms:                         0
% 3.46/0.98  pred_elim_cands:                        1
% 3.46/0.98  pred_elim:                              10
% 3.46/0.98  pred_elim_cl:                           20
% 3.46/0.98  pred_elim_cycles:                       15
% 3.46/0.98  merged_defs:                            0
% 3.46/0.98  merged_defs_ncl:                        0
% 3.46/0.98  bin_hyper_res:                          0
% 3.46/0.98  prep_cycles:                            4
% 3.46/0.98  pred_elim_time:                         0.015
% 3.46/0.98  splitting_time:                         0.
% 3.46/0.98  sem_filter_time:                        0.
% 3.46/0.98  monotx_time:                            0.001
% 3.46/0.98  subtype_inf_time:                       0.
% 3.46/0.98  
% 3.46/0.98  ------ Problem properties
% 3.46/0.98  
% 3.46/0.98  clauses:                                14
% 3.46/0.98  conjectures:                            6
% 3.46/0.98  epr:                                    1
% 3.46/0.98  horn:                                   14
% 3.46/0.98  ground:                                 6
% 3.46/0.98  unary:                                  6
% 3.46/0.98  binary:                                 2
% 3.46/0.98  lits:                                   29
% 3.46/0.98  lits_eq:                                12
% 3.46/0.98  fd_pure:                                0
% 3.46/0.98  fd_pseudo:                              0
% 3.46/0.98  fd_cond:                                0
% 3.46/0.98  fd_pseudo_cond:                         1
% 3.46/0.98  ac_symbols:                             0
% 3.46/0.98  
% 3.46/0.98  ------ Propositional Solver
% 3.46/0.98  
% 3.46/0.98  prop_solver_calls:                      30
% 3.46/0.98  prop_fast_solver_calls:                 894
% 3.46/0.98  smt_solver_calls:                       0
% 3.46/0.98  smt_fast_solver_calls:                  0
% 3.46/0.98  prop_num_of_clauses:                    3898
% 3.46/0.98  prop_preprocess_simplified:             7931
% 3.46/0.98  prop_fo_subsumed:                       28
% 3.46/0.98  prop_solver_time:                       0.
% 3.46/0.98  smt_solver_time:                        0.
% 3.46/0.98  smt_fast_solver_time:                   0.
% 3.46/0.98  prop_fast_solver_time:                  0.
% 3.46/0.98  prop_unsat_core_time:                   0.
% 3.46/0.98  
% 3.46/0.98  ------ QBF
% 3.46/0.98  
% 3.46/0.98  qbf_q_res:                              0
% 3.46/0.98  qbf_num_tautologies:                    0
% 3.46/0.98  qbf_prep_cycles:                        0
% 3.46/0.98  
% 3.46/0.98  ------ BMC1
% 3.46/0.98  
% 3.46/0.98  bmc1_current_bound:                     -1
% 3.46/0.98  bmc1_last_solved_bound:                 -1
% 3.46/0.98  bmc1_unsat_core_size:                   -1
% 3.46/0.98  bmc1_unsat_core_parents_size:           -1
% 3.46/0.98  bmc1_merge_next_fun:                    0
% 3.46/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.46/0.98  
% 3.46/0.98  ------ Instantiation
% 3.46/0.98  
% 3.46/0.98  inst_num_of_clauses:                    1469
% 3.46/0.98  inst_num_in_passive:                    283
% 3.46/0.98  inst_num_in_active:                     574
% 3.46/0.98  inst_num_in_unprocessed:                612
% 3.46/0.98  inst_num_of_loops:                      660
% 3.46/0.98  inst_num_of_learning_restarts:          0
% 3.46/0.98  inst_num_moves_active_passive:          84
% 3.46/0.98  inst_lit_activity:                      0
% 3.46/0.98  inst_lit_activity_moves:                1
% 3.46/0.98  inst_num_tautologies:                   0
% 3.46/0.98  inst_num_prop_implied:                  0
% 3.46/0.98  inst_num_existing_simplified:           0
% 3.46/0.98  inst_num_eq_res_simplified:             0
% 3.46/0.98  inst_num_child_elim:                    0
% 3.46/0.98  inst_num_of_dismatching_blockings:      331
% 3.46/0.98  inst_num_of_non_proper_insts:           1032
% 3.46/0.98  inst_num_of_duplicates:                 0
% 3.46/0.98  inst_inst_num_from_inst_to_res:         0
% 3.46/0.98  inst_dismatching_checking_time:         0.
% 3.46/0.98  
% 3.46/0.98  ------ Resolution
% 3.46/0.98  
% 3.46/0.98  res_num_of_clauses:                     0
% 3.46/0.98  res_num_in_passive:                     0
% 3.46/0.98  res_num_in_active:                      0
% 3.46/0.98  res_num_of_loops:                       97
% 3.46/0.98  res_forward_subset_subsumed:            49
% 3.46/0.98  res_backward_subset_subsumed:           0
% 3.46/0.98  res_forward_subsumed:                   0
% 3.46/0.98  res_backward_subsumed:                  0
% 3.46/0.98  res_forward_subsumption_resolution:     0
% 3.46/0.98  res_backward_subsumption_resolution:    0
% 3.46/0.98  res_clause_to_clause_subsumption:       343
% 3.46/0.98  res_orphan_elimination:                 0
% 3.46/0.98  res_tautology_del:                      20
% 3.46/0.98  res_num_eq_res_simplified:              0
% 3.46/0.98  res_num_sel_changes:                    0
% 3.46/0.98  res_moves_from_active_to_pass:          0
% 3.46/0.98  
% 3.46/0.98  ------ Superposition
% 3.46/0.98  
% 3.46/0.98  sup_time_total:                         0.
% 3.46/0.98  sup_time_generating:                    0.
% 3.46/0.98  sup_time_sim_full:                      0.
% 3.46/0.98  sup_time_sim_immed:                     0.
% 3.46/0.98  
% 3.46/0.98  sup_num_of_clauses:                     55
% 3.46/0.98  sup_num_in_active:                      48
% 3.46/0.98  sup_num_in_passive:                     7
% 3.46/0.98  sup_num_of_loops:                       130
% 3.46/0.98  sup_fw_superposition:                   111
% 3.46/0.98  sup_bw_superposition:                   0
% 3.46/0.98  sup_immediate_simplified:               43
% 3.46/0.98  sup_given_eliminated:                   0
% 3.46/0.98  comparisons_done:                       0
% 3.46/0.98  comparisons_avoided:                    0
% 3.46/0.98  
% 3.46/0.98  ------ Simplifications
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  sim_fw_subset_subsumed:                 0
% 3.46/0.98  sim_bw_subset_subsumed:                 0
% 3.46/0.98  sim_fw_subsumed:                        0
% 3.46/0.98  sim_bw_subsumed:                        0
% 3.46/0.98  sim_fw_subsumption_res:                 0
% 3.46/0.98  sim_bw_subsumption_res:                 0
% 3.46/0.98  sim_tautology_del:                      0
% 3.46/0.98  sim_eq_tautology_del:                   20
% 3.46/0.98  sim_eq_res_simp:                        0
% 3.46/0.98  sim_fw_demodulated:                     0
% 3.46/0.98  sim_bw_demodulated:                     83
% 3.46/0.98  sim_light_normalised:                   62
% 3.46/0.98  sim_joinable_taut:                      0
% 3.46/0.98  sim_joinable_simp:                      0
% 3.46/0.98  sim_ac_normalised:                      0
% 3.46/0.98  sim_smt_subsumption:                    0
% 3.46/0.98  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:14 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  225 (3312 expanded)
%              Number of clauses        :  156 ( 775 expanded)
%              Number of leaves         :   19 (1149 expanded)
%              Depth                    :   24
%              Number of atoms          :  844 (25970 expanded)
%              Number of equality atoms :  262 (8873 expanded)
%              Maximal formula depth    :   13 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK5 != X2
        & k3_lattices(X0,X1,sK5) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK5) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
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
            ( sK4 != X3
            & k3_lattices(X0,X1,sK4) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK4) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
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
                & k3_lattices(X0,sK3,X2) = k3_lattices(X0,sK3,X3)
                & k4_lattices(X0,sK3,X2) = k4_lattices(X0,sK3,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
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
                  & k3_lattices(sK2,X1,X2) = k3_lattices(sK2,X1,X3)
                  & k4_lattices(sK2,X1,X2) = k4_lattices(sK2,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v11_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( sK4 != sK5
    & k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5)
    & k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5)
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v11_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f35,f44,f43,f42,f41])).

fof(f70,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
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
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    v11_lattices(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(pure_predicate_removal,[],[f1])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK1(X0))) != X1
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),X2)) != sK0(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),sK1(X0))) != sK0(X0)
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f53,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_714,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_942,plain,
    ( sK5 != X0_50
    | sK4 != X0_50
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_14657,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_708,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_909,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_707,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_910,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_706,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_911,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,negated_conjecture,
    ( v11_lattices(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_27,c_26,c_24])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k4_lattices(sK2,k3_lattices(sK2,X2,X0),k3_lattices(sK2,X2,X1)) = k3_lattices(sK2,X2,k4_lattices(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK2))
    | k4_lattices(sK2,k3_lattices(sK2,X2_50,X0_50),k3_lattices(sK2,X2_50,X1_50)) = k3_lattices(sK2,X2_50,k4_lattices(sK2,X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_912,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,X0_50,X1_50),k3_lattices(sK2,X0_50,X2_50)) = k3_lattices(sK2,X0_50,k4_lattices(sK2,X1_50,X2_50))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_1095,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,X0_50,X1_50),k3_lattices(sK2,X0_50,sK3)) = k3_lattices(sK2,X0_50,k4_lattices(sK2,X1_50,sK3))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_912])).

cnf(c_4711,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,X0_50),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK4,k4_lattices(sK2,X0_50,sK3))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_1095])).

cnf(c_6371,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK5),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK4,k4_lattices(sK2,sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_909,c_4711])).

cnf(c_13,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_6])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_408,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_409,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_79,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_411,plain,
    ( v6_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_27,c_26,c_24,c_79])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_360,c_411])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k4_lattices(sK2,X0,X1) = k4_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,X0,X1) = k4_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_27,c_24])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | k4_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_462])).

cnf(c_914,plain,
    ( k4_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X1_50,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_1464,plain,
    ( k4_lattices(sK2,X0_50,sK4) = k4_lattices(sK2,sK4,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_914])).

cnf(c_1910,plain,
    ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_911,c_1464])).

cnf(c_1463,plain,
    ( k4_lattices(sK2,sK5,X0_50) = k4_lattices(sK2,X0_50,sK5)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_914])).

cnf(c_1700,plain,
    ( k4_lattices(sK2,sK5,sK3) = k4_lattices(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_911,c_1463])).

cnf(c_20,negated_conjecture,
    ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_709,negated_conjecture,
    ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1794,plain,
    ( k4_lattices(sK2,sK5,sK3) = k4_lattices(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1700,c_709])).

cnf(c_1911,plain,
    ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_1910,c_1794])).

cnf(c_4710,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),k3_lattices(sK2,sK5,sK3)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK3))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_1095])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | ~ v4_lattices(sK2)
    | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_12,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_51,plain,
    ( l2_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_76,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_27,c_26,c_24,c_51,c_76])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | k3_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_594])).

cnf(c_919,plain,
    ( k3_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X1_50,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_3279,plain,
    ( k3_lattices(sK2,sK4,X0_50) = k3_lattices(sK2,X0_50,sK4)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_919])).

cnf(c_4824,plain,
    ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_911,c_3279])).

cnf(c_3278,plain,
    ( k3_lattices(sK2,sK5,X0_50) = k3_lattices(sK2,X0_50,sK5)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_919])).

cnf(c_3723,plain,
    ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_911,c_3278])).

cnf(c_19,negated_conjecture,
    ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_710,negated_conjecture,
    ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3898,plain,
    ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3723,c_710])).

cnf(c_4830,plain,
    ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_4824,c_3898])).

cnf(c_5850,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK3))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4710,c_4830])).

cnf(c_5855,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK4),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK5,k4_lattices(sK2,sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_910,c_5850])).

cnf(c_3722,plain,
    ( k3_lattices(sK2,sK5,sK4) = k3_lattices(sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_910,c_3278])).

cnf(c_1093,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,X0_50,X1_50),k3_lattices(sK2,X0_50,sK5)) = k3_lattices(sK2,X0_50,k4_lattices(sK2,X1_50,sK5))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_912])).

cnf(c_1123,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),k3_lattices(sK2,sK5,sK5)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK5))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_1093])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | ~ v4_lattices(sK2)
    | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_27,c_26,c_24,c_51,c_76])).

cnf(c_700,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | k1_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_552])).

cnf(c_917,plain,
    ( k1_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_2249,plain,
    ( k1_lattices(sK2,sK5,X0_50) = k3_lattices(sK2,sK5,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_917])).

cnf(c_2362,plain,
    ( k1_lattices(sK2,sK5,sK5) = k3_lattices(sK2,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_909,c_2249])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v9_lattices(X1)
    | X1 != X2
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_302,c_0,c_2])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_26])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k1_lattices(sK2,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_lattices(sK2,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_27,c_24])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | k1_lattices(sK2,X0_50,X0_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_913,plain,
    ( k1_lattices(sK2,X0_50,X0_50) = X0_50
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1053,plain,
    ( k1_lattices(sK2,sK5,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_909,c_913])).

cnf(c_2365,plain,
    ( k3_lattices(sK2,sK5,sK5) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_2362,c_1053])).

cnf(c_5530,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),sK5) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK5))
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1123,c_2365])).

cnf(c_5536,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),sK5) = k3_lattices(sK2,sK5,k4_lattices(sK2,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_911,c_5530])).

cnf(c_1969,plain,
    ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_1911,c_1700])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k3_lattices(sK2,X0,X1),u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | ~ v4_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k3_lattices(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_27,c_26,c_24,c_51,c_76])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | m1_subset_1(k3_lattices(sK2,X0_50,X1_50),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_918,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_lattices(sK2,X0_50,X1_50),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_2519,plain,
    ( m1_subset_1(k3_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_918])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2683,plain,
    ( m1_subset_1(k3_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2519,c_32,c_34])).

cnf(c_2695,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK3,sK4),sK5) = k4_lattices(sK2,sK5,k3_lattices(sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2683,c_1463])).

cnf(c_4076,plain,
    ( k4_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),sK5) ),
    inference(demodulation,[status(thm)],[c_3898,c_2695])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_411])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k2_lattices(sK2,X0,X1) = k4_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = k4_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_27,c_24])).

cnf(c_702,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | k2_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_915,plain,
    ( k2_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1959,plain,
    ( k2_lattices(sK2,sK5,X0_50) = k4_lattices(sK2,sK5,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_915])).

cnf(c_2691,plain,
    ( k2_lattices(sK2,sK5,k3_lattices(sK2,sK3,sK4)) = k4_lattices(sK2,sK5,k3_lattices(sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2683,c_1959])).

cnf(c_4082,plain,
    ( k2_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = k4_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) ),
    inference(demodulation,[status(thm)],[c_3898,c_2691])).

cnf(c_2364,plain,
    ( k1_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_911,c_2249])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v9_lattices(sK2)
    | k2_lattices(sK2,X0,k1_lattices(sK2,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_85,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v9_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,k1_lattices(sK2,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_27,c_26,c_24,c_85])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
    | k2_lattices(sK2,X0_50,k1_lattices(sK2,X0_50,X1_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_525])).

cnf(c_916,plain,
    ( k2_lattices(sK2,X0_50,k1_lattices(sK2,X0_50,X1_50)) = X0_50
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1321,plain,
    ( k2_lattices(sK2,sK5,k1_lattices(sK2,sK5,X0_50)) = sK5
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_916])).

cnf(c_1431,plain,
    ( k2_lattices(sK2,sK5,k1_lattices(sK2,sK5,sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_911,c_1321])).

cnf(c_2517,plain,
    ( k2_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2364,c_1431])).

cnf(c_4091,plain,
    ( k4_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_4082,c_2517])).

cnf(c_4093,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_4076,c_4091])).

cnf(c_5538,plain,
    ( k3_lattices(sK2,sK5,k4_lattices(sK2,sK4,sK3)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_5536,c_1969,c_4093])).

cnf(c_5859,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK5),k3_lattices(sK2,sK4,sK3)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_5855,c_3722,c_5538])).

cnf(c_6377,plain,
    ( k3_lattices(sK2,sK4,k4_lattices(sK2,sK4,sK3)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_6371,c_1911,c_5859])).

cnf(c_6372,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK4),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK4,k4_lattices(sK2,sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_910,c_4711])).

cnf(c_2250,plain,
    ( k1_lattices(sK2,sK4,X0_50) = k3_lattices(sK2,sK4,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_917])).

cnf(c_2727,plain,
    ( k1_lattices(sK2,sK4,sK4) = k3_lattices(sK2,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_910,c_2250])).

cnf(c_1054,plain,
    ( k1_lattices(sK2,sK4,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_910,c_913])).

cnf(c_2731,plain,
    ( k3_lattices(sK2,sK4,sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2727,c_1054])).

cnf(c_1960,plain,
    ( k2_lattices(sK2,sK4,X0_50) = k4_lattices(sK2,sK4,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_915])).

cnf(c_2690,plain,
    ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK3,sK4)) = k4_lattices(sK2,sK4,k3_lattices(sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2683,c_1960])).

cnf(c_4083,plain,
    ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK5,sK3)) = k4_lattices(sK2,sK4,k3_lattices(sK2,sK5,sK3)) ),
    inference(demodulation,[status(thm)],[c_3898,c_2690])).

cnf(c_4895,plain,
    ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) = k4_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_4830,c_4083])).

cnf(c_2728,plain,
    ( k1_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_911,c_2250])).

cnf(c_1322,plain,
    ( k2_lattices(sK2,sK4,k1_lattices(sK2,sK4,X0_50)) = sK4
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_916])).

cnf(c_1511,plain,
    ( k2_lattices(sK2,sK4,k1_lattices(sK2,sK4,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_911,c_1322])).

cnf(c_2811,plain,
    ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_2728,c_1511])).

cnf(c_4907,plain,
    ( k4_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_4895,c_2811])).

cnf(c_6376,plain,
    ( k3_lattices(sK2,sK4,k4_lattices(sK2,sK4,sK3)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_6372,c_2731,c_4907])).

cnf(c_10653,plain,
    ( sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_6377,c_6376])).

cnf(c_713,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1120,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_18,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_711,negated_conjecture,
    ( sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14657,c_10653,c_1120,c_711])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.12/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/1.50  
% 7.12/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.50  
% 7.12/1.50  ------  iProver source info
% 7.12/1.50  
% 7.12/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.50  git: non_committed_changes: false
% 7.12/1.50  git: last_make_outside_of_git: false
% 7.12/1.50  
% 7.12/1.50  ------ 
% 7.12/1.50  
% 7.12/1.50  ------ Input Options
% 7.12/1.50  
% 7.12/1.50  --out_options                           all
% 7.12/1.50  --tptp_safe_out                         true
% 7.12/1.50  --problem_path                          ""
% 7.12/1.50  --include_path                          ""
% 7.12/1.50  --clausifier                            res/vclausify_rel
% 7.12/1.50  --clausifier_options                    ""
% 7.12/1.50  --stdin                                 false
% 7.12/1.50  --stats_out                             all
% 7.12/1.50  
% 7.12/1.50  ------ General Options
% 7.12/1.50  
% 7.12/1.50  --fof                                   false
% 7.12/1.50  --time_out_real                         305.
% 7.12/1.50  --time_out_virtual                      -1.
% 7.12/1.50  --symbol_type_check                     false
% 7.12/1.50  --clausify_out                          false
% 7.12/1.50  --sig_cnt_out                           false
% 7.12/1.50  --trig_cnt_out                          false
% 7.12/1.50  --trig_cnt_out_tolerance                1.
% 7.12/1.50  --trig_cnt_out_sk_spl                   false
% 7.12/1.50  --abstr_cl_out                          false
% 7.12/1.50  
% 7.12/1.50  ------ Global Options
% 7.12/1.50  
% 7.12/1.50  --schedule                              default
% 7.12/1.50  --add_important_lit                     false
% 7.12/1.50  --prop_solver_per_cl                    1000
% 7.12/1.50  --min_unsat_core                        false
% 7.12/1.50  --soft_assumptions                      false
% 7.12/1.50  --soft_lemma_size                       3
% 7.12/1.50  --prop_impl_unit_size                   0
% 7.12/1.50  --prop_impl_unit                        []
% 7.12/1.50  --share_sel_clauses                     true
% 7.12/1.50  --reset_solvers                         false
% 7.12/1.50  --bc_imp_inh                            [conj_cone]
% 7.12/1.50  --conj_cone_tolerance                   3.
% 7.12/1.50  --extra_neg_conj                        none
% 7.12/1.50  --large_theory_mode                     true
% 7.12/1.50  --prolific_symb_bound                   200
% 7.12/1.50  --lt_threshold                          2000
% 7.12/1.50  --clause_weak_htbl                      true
% 7.12/1.50  --gc_record_bc_elim                     false
% 7.12/1.50  
% 7.12/1.50  ------ Preprocessing Options
% 7.12/1.50  
% 7.12/1.50  --preprocessing_flag                    true
% 7.12/1.50  --time_out_prep_mult                    0.1
% 7.12/1.50  --splitting_mode                        input
% 7.12/1.50  --splitting_grd                         true
% 7.12/1.50  --splitting_cvd                         false
% 7.12/1.50  --splitting_cvd_svl                     false
% 7.12/1.50  --splitting_nvd                         32
% 7.12/1.50  --sub_typing                            true
% 7.12/1.50  --prep_gs_sim                           true
% 7.12/1.50  --prep_unflatten                        true
% 7.12/1.50  --prep_res_sim                          true
% 7.12/1.50  --prep_upred                            true
% 7.12/1.50  --prep_sem_filter                       exhaustive
% 7.12/1.50  --prep_sem_filter_out                   false
% 7.12/1.50  --pred_elim                             true
% 7.12/1.50  --res_sim_input                         true
% 7.12/1.50  --eq_ax_congr_red                       true
% 7.12/1.50  --pure_diseq_elim                       true
% 7.12/1.50  --brand_transform                       false
% 7.12/1.50  --non_eq_to_eq                          false
% 7.12/1.50  --prep_def_merge                        true
% 7.12/1.50  --prep_def_merge_prop_impl              false
% 7.12/1.50  --prep_def_merge_mbd                    true
% 7.12/1.50  --prep_def_merge_tr_red                 false
% 7.12/1.50  --prep_def_merge_tr_cl                  false
% 7.12/1.50  --smt_preprocessing                     true
% 7.12/1.50  --smt_ac_axioms                         fast
% 7.12/1.50  --preprocessed_out                      false
% 7.12/1.50  --preprocessed_stats                    false
% 7.12/1.50  
% 7.12/1.50  ------ Abstraction refinement Options
% 7.12/1.50  
% 7.12/1.50  --abstr_ref                             []
% 7.12/1.50  --abstr_ref_prep                        false
% 7.12/1.50  --abstr_ref_until_sat                   false
% 7.12/1.50  --abstr_ref_sig_restrict                funpre
% 7.12/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.50  --abstr_ref_under                       []
% 7.12/1.50  
% 7.12/1.50  ------ SAT Options
% 7.12/1.50  
% 7.12/1.50  --sat_mode                              false
% 7.12/1.50  --sat_fm_restart_options                ""
% 7.12/1.50  --sat_gr_def                            false
% 7.12/1.50  --sat_epr_types                         true
% 7.12/1.50  --sat_non_cyclic_types                  false
% 7.12/1.50  --sat_finite_models                     false
% 7.12/1.50  --sat_fm_lemmas                         false
% 7.12/1.50  --sat_fm_prep                           false
% 7.12/1.50  --sat_fm_uc_incr                        true
% 7.12/1.50  --sat_out_model                         small
% 7.12/1.50  --sat_out_clauses                       false
% 7.12/1.50  
% 7.12/1.50  ------ QBF Options
% 7.12/1.50  
% 7.12/1.50  --qbf_mode                              false
% 7.12/1.50  --qbf_elim_univ                         false
% 7.12/1.50  --qbf_dom_inst                          none
% 7.12/1.50  --qbf_dom_pre_inst                      false
% 7.12/1.50  --qbf_sk_in                             false
% 7.12/1.50  --qbf_pred_elim                         true
% 7.12/1.50  --qbf_split                             512
% 7.12/1.50  
% 7.12/1.50  ------ BMC1 Options
% 7.12/1.50  
% 7.12/1.50  --bmc1_incremental                      false
% 7.12/1.50  --bmc1_axioms                           reachable_all
% 7.12/1.50  --bmc1_min_bound                        0
% 7.12/1.50  --bmc1_max_bound                        -1
% 7.12/1.50  --bmc1_max_bound_default                -1
% 7.12/1.50  --bmc1_symbol_reachability              true
% 7.12/1.50  --bmc1_property_lemmas                  false
% 7.12/1.50  --bmc1_k_induction                      false
% 7.12/1.50  --bmc1_non_equiv_states                 false
% 7.12/1.50  --bmc1_deadlock                         false
% 7.12/1.50  --bmc1_ucm                              false
% 7.12/1.50  --bmc1_add_unsat_core                   none
% 7.12/1.50  --bmc1_unsat_core_children              false
% 7.12/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.50  --bmc1_out_stat                         full
% 7.12/1.50  --bmc1_ground_init                      false
% 7.12/1.50  --bmc1_pre_inst_next_state              false
% 7.12/1.50  --bmc1_pre_inst_state                   false
% 7.12/1.50  --bmc1_pre_inst_reach_state             false
% 7.12/1.50  --bmc1_out_unsat_core                   false
% 7.12/1.50  --bmc1_aig_witness_out                  false
% 7.12/1.50  --bmc1_verbose                          false
% 7.12/1.50  --bmc1_dump_clauses_tptp                false
% 7.12/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.50  --bmc1_dump_file                        -
% 7.12/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.50  --bmc1_ucm_extend_mode                  1
% 7.12/1.50  --bmc1_ucm_init_mode                    2
% 7.12/1.50  --bmc1_ucm_cone_mode                    none
% 7.12/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.50  --bmc1_ucm_relax_model                  4
% 7.12/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.50  --bmc1_ucm_layered_model                none
% 7.12/1.50  --bmc1_ucm_max_lemma_size               10
% 7.12/1.50  
% 7.12/1.50  ------ AIG Options
% 7.12/1.50  
% 7.12/1.50  --aig_mode                              false
% 7.12/1.50  
% 7.12/1.50  ------ Instantiation Options
% 7.12/1.50  
% 7.12/1.50  --instantiation_flag                    true
% 7.12/1.50  --inst_sos_flag                         true
% 7.12/1.50  --inst_sos_phase                        true
% 7.12/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.50  --inst_lit_sel_side                     num_symb
% 7.12/1.50  --inst_solver_per_active                1400
% 7.12/1.50  --inst_solver_calls_frac                1.
% 7.12/1.50  --inst_passive_queue_type               priority_queues
% 7.12/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.50  --inst_passive_queues_freq              [25;2]
% 7.12/1.50  --inst_dismatching                      true
% 7.12/1.50  --inst_eager_unprocessed_to_passive     true
% 7.12/1.50  --inst_prop_sim_given                   true
% 7.12/1.50  --inst_prop_sim_new                     false
% 7.12/1.50  --inst_subs_new                         false
% 7.12/1.50  --inst_eq_res_simp                      false
% 7.12/1.50  --inst_subs_given                       false
% 7.12/1.50  --inst_orphan_elimination               true
% 7.12/1.50  --inst_learning_loop_flag               true
% 7.12/1.50  --inst_learning_start                   3000
% 7.12/1.50  --inst_learning_factor                  2
% 7.12/1.50  --inst_start_prop_sim_after_learn       3
% 7.12/1.50  --inst_sel_renew                        solver
% 7.12/1.50  --inst_lit_activity_flag                true
% 7.12/1.50  --inst_restr_to_given                   false
% 7.12/1.50  --inst_activity_threshold               500
% 7.12/1.50  --inst_out_proof                        true
% 7.12/1.50  
% 7.12/1.50  ------ Resolution Options
% 7.12/1.50  
% 7.12/1.50  --resolution_flag                       true
% 7.12/1.50  --res_lit_sel                           adaptive
% 7.12/1.50  --res_lit_sel_side                      none
% 7.12/1.50  --res_ordering                          kbo
% 7.12/1.50  --res_to_prop_solver                    active
% 7.12/1.50  --res_prop_simpl_new                    false
% 7.12/1.50  --res_prop_simpl_given                  true
% 7.12/1.50  --res_passive_queue_type                priority_queues
% 7.12/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.50  --res_passive_queues_freq               [15;5]
% 7.12/1.50  --res_forward_subs                      full
% 7.12/1.50  --res_backward_subs                     full
% 7.12/1.50  --res_forward_subs_resolution           true
% 7.12/1.50  --res_backward_subs_resolution          true
% 7.12/1.50  --res_orphan_elimination                true
% 7.12/1.50  --res_time_limit                        2.
% 7.12/1.50  --res_out_proof                         true
% 7.12/1.50  
% 7.12/1.50  ------ Superposition Options
% 7.12/1.50  
% 7.12/1.50  --superposition_flag                    true
% 7.12/1.50  --sup_passive_queue_type                priority_queues
% 7.12/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.50  --demod_completeness_check              fast
% 7.12/1.50  --demod_use_ground                      true
% 7.12/1.50  --sup_to_prop_solver                    passive
% 7.12/1.50  --sup_prop_simpl_new                    true
% 7.12/1.50  --sup_prop_simpl_given                  true
% 7.12/1.50  --sup_fun_splitting                     true
% 7.12/1.50  --sup_smt_interval                      50000
% 7.12/1.50  
% 7.12/1.50  ------ Superposition Simplification Setup
% 7.12/1.50  
% 7.12/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.12/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.12/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.12/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.12/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.12/1.50  --sup_immed_triv                        [TrivRules]
% 7.12/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.50  --sup_immed_bw_main                     []
% 7.12/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.12/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.50  --sup_input_bw                          []
% 7.12/1.50  
% 7.12/1.50  ------ Combination Options
% 7.12/1.50  
% 7.12/1.50  --comb_res_mult                         3
% 7.12/1.50  --comb_sup_mult                         2
% 7.12/1.50  --comb_inst_mult                        10
% 7.12/1.50  
% 7.12/1.50  ------ Debug Options
% 7.12/1.50  
% 7.12/1.50  --dbg_backtrace                         false
% 7.12/1.50  --dbg_dump_prop_clauses                 false
% 7.12/1.50  --dbg_dump_prop_clauses_file            -
% 7.12/1.50  --dbg_out_stat                          false
% 7.12/1.50  ------ Parsing...
% 7.12/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.12/1.50  
% 7.12/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.12/1.50  
% 7.12/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.12/1.50  
% 7.12/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.12/1.50  ------ Proving...
% 7.12/1.50  ------ Problem Properties 
% 7.12/1.50  
% 7.12/1.50  
% 7.12/1.50  clauses                                 14
% 7.12/1.50  conjectures                             6
% 7.12/1.50  EPR                                     1
% 7.12/1.50  Horn                                    14
% 7.12/1.50  unary                                   6
% 7.12/1.50  binary                                  1
% 7.12/1.50  lits                                    30
% 7.12/1.50  lits eq                                 10
% 7.12/1.50  fd_pure                                 0
% 7.12/1.50  fd_pseudo                               0
% 7.12/1.50  fd_cond                                 0
% 7.12/1.50  fd_pseudo_cond                          0
% 7.12/1.50  AC symbols                              0
% 7.12/1.50  
% 7.12/1.50  ------ Schedule dynamic 5 is on 
% 7.12/1.50  
% 7.12/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.12/1.50  
% 7.12/1.50  
% 7.12/1.50  ------ 
% 7.12/1.50  Current options:
% 7.12/1.50  ------ 
% 7.12/1.50  
% 7.12/1.50  ------ Input Options
% 7.12/1.50  
% 7.12/1.50  --out_options                           all
% 7.12/1.50  --tptp_safe_out                         true
% 7.12/1.50  --problem_path                          ""
% 7.12/1.50  --include_path                          ""
% 7.12/1.50  --clausifier                            res/vclausify_rel
% 7.12/1.50  --clausifier_options                    ""
% 7.12/1.50  --stdin                                 false
% 7.12/1.50  --stats_out                             all
% 7.12/1.50  
% 7.12/1.50  ------ General Options
% 7.12/1.50  
% 7.12/1.50  --fof                                   false
% 7.12/1.50  --time_out_real                         305.
% 7.12/1.50  --time_out_virtual                      -1.
% 7.12/1.50  --symbol_type_check                     false
% 7.12/1.50  --clausify_out                          false
% 7.12/1.50  --sig_cnt_out                           false
% 7.12/1.50  --trig_cnt_out                          false
% 7.12/1.50  --trig_cnt_out_tolerance                1.
% 7.12/1.50  --trig_cnt_out_sk_spl                   false
% 7.12/1.50  --abstr_cl_out                          false
% 7.12/1.50  
% 7.12/1.50  ------ Global Options
% 7.12/1.50  
% 7.12/1.50  --schedule                              default
% 7.12/1.50  --add_important_lit                     false
% 7.12/1.50  --prop_solver_per_cl                    1000
% 7.12/1.50  --min_unsat_core                        false
% 7.12/1.50  --soft_assumptions                      false
% 7.12/1.50  --soft_lemma_size                       3
% 7.12/1.50  --prop_impl_unit_size                   0
% 7.12/1.50  --prop_impl_unit                        []
% 7.12/1.50  --share_sel_clauses                     true
% 7.12/1.50  --reset_solvers                         false
% 7.12/1.50  --bc_imp_inh                            [conj_cone]
% 7.12/1.50  --conj_cone_tolerance                   3.
% 7.12/1.50  --extra_neg_conj                        none
% 7.12/1.50  --large_theory_mode                     true
% 7.12/1.50  --prolific_symb_bound                   200
% 7.12/1.50  --lt_threshold                          2000
% 7.12/1.50  --clause_weak_htbl                      true
% 7.12/1.50  --gc_record_bc_elim                     false
% 7.12/1.50  
% 7.12/1.50  ------ Preprocessing Options
% 7.12/1.50  
% 7.12/1.50  --preprocessing_flag                    true
% 7.12/1.50  --time_out_prep_mult                    0.1
% 7.12/1.50  --splitting_mode                        input
% 7.12/1.50  --splitting_grd                         true
% 7.12/1.50  --splitting_cvd                         false
% 7.12/1.50  --splitting_cvd_svl                     false
% 7.12/1.50  --splitting_nvd                         32
% 7.12/1.50  --sub_typing                            true
% 7.12/1.50  --prep_gs_sim                           true
% 7.12/1.50  --prep_unflatten                        true
% 7.12/1.50  --prep_res_sim                          true
% 7.12/1.50  --prep_upred                            true
% 7.12/1.50  --prep_sem_filter                       exhaustive
% 7.12/1.50  --prep_sem_filter_out                   false
% 7.12/1.50  --pred_elim                             true
% 7.12/1.50  --res_sim_input                         true
% 7.12/1.50  --eq_ax_congr_red                       true
% 7.12/1.50  --pure_diseq_elim                       true
% 7.12/1.50  --brand_transform                       false
% 7.12/1.50  --non_eq_to_eq                          false
% 7.12/1.50  --prep_def_merge                        true
% 7.12/1.50  --prep_def_merge_prop_impl              false
% 7.12/1.50  --prep_def_merge_mbd                    true
% 7.12/1.50  --prep_def_merge_tr_red                 false
% 7.12/1.50  --prep_def_merge_tr_cl                  false
% 7.12/1.50  --smt_preprocessing                     true
% 7.12/1.50  --smt_ac_axioms                         fast
% 7.12/1.50  --preprocessed_out                      false
% 7.12/1.50  --preprocessed_stats                    false
% 7.12/1.50  
% 7.12/1.50  ------ Abstraction refinement Options
% 7.12/1.50  
% 7.12/1.50  --abstr_ref                             []
% 7.12/1.50  --abstr_ref_prep                        false
% 7.12/1.50  --abstr_ref_until_sat                   false
% 7.12/1.50  --abstr_ref_sig_restrict                funpre
% 7.12/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.50  --abstr_ref_under                       []
% 7.12/1.50  
% 7.12/1.50  ------ SAT Options
% 7.12/1.50  
% 7.12/1.50  --sat_mode                              false
% 7.12/1.50  --sat_fm_restart_options                ""
% 7.12/1.50  --sat_gr_def                            false
% 7.12/1.50  --sat_epr_types                         true
% 7.12/1.50  --sat_non_cyclic_types                  false
% 7.12/1.50  --sat_finite_models                     false
% 7.12/1.50  --sat_fm_lemmas                         false
% 7.12/1.50  --sat_fm_prep                           false
% 7.12/1.50  --sat_fm_uc_incr                        true
% 7.12/1.50  --sat_out_model                         small
% 7.12/1.50  --sat_out_clauses                       false
% 7.12/1.50  
% 7.12/1.50  ------ QBF Options
% 7.12/1.50  
% 7.12/1.50  --qbf_mode                              false
% 7.12/1.50  --qbf_elim_univ                         false
% 7.12/1.50  --qbf_dom_inst                          none
% 7.12/1.50  --qbf_dom_pre_inst                      false
% 7.12/1.50  --qbf_sk_in                             false
% 7.12/1.50  --qbf_pred_elim                         true
% 7.12/1.50  --qbf_split                             512
% 7.12/1.50  
% 7.12/1.50  ------ BMC1 Options
% 7.12/1.50  
% 7.12/1.50  --bmc1_incremental                      false
% 7.12/1.50  --bmc1_axioms                           reachable_all
% 7.12/1.50  --bmc1_min_bound                        0
% 7.12/1.50  --bmc1_max_bound                        -1
% 7.12/1.50  --bmc1_max_bound_default                -1
% 7.12/1.50  --bmc1_symbol_reachability              true
% 7.12/1.50  --bmc1_property_lemmas                  false
% 7.12/1.50  --bmc1_k_induction                      false
% 7.12/1.50  --bmc1_non_equiv_states                 false
% 7.12/1.50  --bmc1_deadlock                         false
% 7.12/1.50  --bmc1_ucm                              false
% 7.12/1.50  --bmc1_add_unsat_core                   none
% 7.12/1.50  --bmc1_unsat_core_children              false
% 7.12/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.50  --bmc1_out_stat                         full
% 7.12/1.50  --bmc1_ground_init                      false
% 7.12/1.50  --bmc1_pre_inst_next_state              false
% 7.12/1.50  --bmc1_pre_inst_state                   false
% 7.12/1.50  --bmc1_pre_inst_reach_state             false
% 7.12/1.50  --bmc1_out_unsat_core                   false
% 7.12/1.50  --bmc1_aig_witness_out                  false
% 7.12/1.50  --bmc1_verbose                          false
% 7.12/1.50  --bmc1_dump_clauses_tptp                false
% 7.12/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.50  --bmc1_dump_file                        -
% 7.12/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.50  --bmc1_ucm_extend_mode                  1
% 7.12/1.50  --bmc1_ucm_init_mode                    2
% 7.12/1.50  --bmc1_ucm_cone_mode                    none
% 7.12/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.50  --bmc1_ucm_relax_model                  4
% 7.12/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.50  --bmc1_ucm_layered_model                none
% 7.12/1.50  --bmc1_ucm_max_lemma_size               10
% 7.12/1.50  
% 7.12/1.50  ------ AIG Options
% 7.12/1.50  
% 7.12/1.50  --aig_mode                              false
% 7.12/1.50  
% 7.12/1.50  ------ Instantiation Options
% 7.12/1.50  
% 7.12/1.50  --instantiation_flag                    true
% 7.12/1.50  --inst_sos_flag                         true
% 7.12/1.50  --inst_sos_phase                        true
% 7.12/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.50  --inst_lit_sel_side                     none
% 7.12/1.50  --inst_solver_per_active                1400
% 7.12/1.50  --inst_solver_calls_frac                1.
% 7.12/1.50  --inst_passive_queue_type               priority_queues
% 7.12/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.50  --inst_passive_queues_freq              [25;2]
% 7.12/1.50  --inst_dismatching                      true
% 7.12/1.50  --inst_eager_unprocessed_to_passive     true
% 7.12/1.50  --inst_prop_sim_given                   true
% 7.12/1.50  --inst_prop_sim_new                     false
% 7.12/1.50  --inst_subs_new                         false
% 7.12/1.50  --inst_eq_res_simp                      false
% 7.12/1.50  --inst_subs_given                       false
% 7.12/1.50  --inst_orphan_elimination               true
% 7.12/1.50  --inst_learning_loop_flag               true
% 7.12/1.50  --inst_learning_start                   3000
% 7.12/1.50  --inst_learning_factor                  2
% 7.12/1.50  --inst_start_prop_sim_after_learn       3
% 7.12/1.50  --inst_sel_renew                        solver
% 7.12/1.50  --inst_lit_activity_flag                true
% 7.12/1.50  --inst_restr_to_given                   false
% 7.12/1.50  --inst_activity_threshold               500
% 7.12/1.50  --inst_out_proof                        true
% 7.12/1.50  
% 7.12/1.50  ------ Resolution Options
% 7.12/1.50  
% 7.12/1.50  --resolution_flag                       false
% 7.12/1.50  --res_lit_sel                           adaptive
% 7.12/1.50  --res_lit_sel_side                      none
% 7.12/1.50  --res_ordering                          kbo
% 7.12/1.50  --res_to_prop_solver                    active
% 7.12/1.50  --res_prop_simpl_new                    false
% 7.12/1.50  --res_prop_simpl_given                  true
% 7.12/1.50  --res_passive_queue_type                priority_queues
% 7.12/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.50  --res_passive_queues_freq               [15;5]
% 7.12/1.50  --res_forward_subs                      full
% 7.12/1.50  --res_backward_subs                     full
% 7.12/1.50  --res_forward_subs_resolution           true
% 7.12/1.50  --res_backward_subs_resolution          true
% 7.12/1.50  --res_orphan_elimination                true
% 7.12/1.50  --res_time_limit                        2.
% 7.12/1.50  --res_out_proof                         true
% 7.12/1.50  
% 7.12/1.50  ------ Superposition Options
% 7.12/1.50  
% 7.12/1.50  --superposition_flag                    true
% 7.12/1.50  --sup_passive_queue_type                priority_queues
% 7.12/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.50  --demod_completeness_check              fast
% 7.12/1.50  --demod_use_ground                      true
% 7.12/1.50  --sup_to_prop_solver                    passive
% 7.12/1.50  --sup_prop_simpl_new                    true
% 7.12/1.50  --sup_prop_simpl_given                  true
% 7.12/1.50  --sup_fun_splitting                     true
% 7.12/1.50  --sup_smt_interval                      50000
% 7.12/1.50  
% 7.12/1.50  ------ Superposition Simplification Setup
% 7.12/1.50  
% 7.12/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.12/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.12/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.12/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.12/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.12/1.50  --sup_immed_triv                        [TrivRules]
% 7.12/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.50  --sup_immed_bw_main                     []
% 7.12/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.12/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.50  --sup_input_bw                          []
% 7.12/1.50  
% 7.12/1.50  ------ Combination Options
% 7.12/1.50  
% 7.12/1.50  --comb_res_mult                         3
% 7.12/1.50  --comb_sup_mult                         2
% 7.12/1.50  --comb_inst_mult                        10
% 7.12/1.50  
% 7.12/1.50  ------ Debug Options
% 7.12/1.50  
% 7.12/1.50  --dbg_backtrace                         false
% 7.12/1.50  --dbg_dump_prop_clauses                 false
% 7.12/1.50  --dbg_dump_prop_clauses_file            -
% 7.12/1.50  --dbg_out_stat                          false
% 7.12/1.50  
% 7.12/1.50  
% 7.12/1.50  
% 7.12/1.50  
% 7.12/1.50  ------ Proving...
% 7.12/1.50  
% 7.12/1.50  
% 7.12/1.50  % SZS status Theorem for theBenchmark.p
% 7.12/1.50  
% 7.12/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.12/1.50  
% 7.12/1.50  fof(f11,conjecture,(
% 7.12/1.50    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f12,negated_conjecture,(
% 7.12/1.50    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 7.12/1.50    inference(negated_conjecture,[],[f11])).
% 7.12/1.50  
% 7.12/1.50  fof(f34,plain,(
% 7.12/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f12])).
% 7.12/1.50  
% 7.12/1.50  fof(f35,plain,(
% 7.12/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f34])).
% 7.12/1.50  
% 7.12/1.50  fof(f44,plain,(
% 7.12/1.50    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK5 != X2 & k3_lattices(X0,X1,sK5) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK5) = k4_lattices(X0,X1,X2) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.12/1.50    introduced(choice_axiom,[])).
% 7.12/1.50  
% 7.12/1.50  fof(f43,plain,(
% 7.12/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK4 != X3 & k3_lattices(X0,X1,sK4) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK4) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 7.12/1.50    introduced(choice_axiom,[])).
% 7.12/1.50  
% 7.12/1.50  fof(f42,plain,(
% 7.12/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK3,X2) = k3_lattices(X0,sK3,X3) & k4_lattices(X0,sK3,X2) = k4_lattices(X0,sK3,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 7.12/1.50    introduced(choice_axiom,[])).
% 7.12/1.50  
% 7.12/1.50  fof(f41,plain,(
% 7.12/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK2,X1,X2) = k3_lattices(sK2,X1,X3) & k4_lattices(sK2,X1,X2) = k4_lattices(sK2,X1,X3) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v11_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 7.12/1.50    introduced(choice_axiom,[])).
% 7.12/1.50  
% 7.12/1.50  fof(f45,plain,(
% 7.12/1.50    (((sK4 != sK5 & k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) & k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v11_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 7.12/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f35,f44,f43,f42,f41])).
% 7.12/1.50  
% 7.12/1.50  fof(f70,plain,(
% 7.12/1.50    m1_subset_1(sK5,u1_struct_0(sK2))),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f69,plain,(
% 7.12/1.50    m1_subset_1(sK4,u1_struct_0(sK2))),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f68,plain,(
% 7.12/1.50    m1_subset_1(sK3,u1_struct_0(sK2))),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f10,axiom,(
% 7.12/1.50    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f32,plain,(
% 7.12/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f10])).
% 7.12/1.50  
% 7.12/1.50  fof(f33,plain,(
% 7.12/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f32])).
% 7.12/1.50  
% 7.12/1.50  fof(f63,plain,(
% 7.12/1.50    ( ! [X2,X0,X3,X1] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f33])).
% 7.12/1.50  
% 7.12/1.50  fof(f66,plain,(
% 7.12/1.50    v11_lattices(sK2)),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f64,plain,(
% 7.12/1.50    ~v2_struct_0(sK2)),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f65,plain,(
% 7.12/1.50    v10_lattices(sK2)),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f67,plain,(
% 7.12/1.50    l3_lattices(sK2)),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f6,axiom,(
% 7.12/1.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f25,plain,(
% 7.12/1.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 7.12/1.50    inference(ennf_transformation,[],[f6])).
% 7.12/1.50  
% 7.12/1.50  fof(f58,plain,(
% 7.12/1.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f25])).
% 7.12/1.50  
% 7.12/1.50  fof(f3,axiom,(
% 7.12/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f19,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f3])).
% 7.12/1.50  
% 7.12/1.50  fof(f20,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f19])).
% 7.12/1.50  
% 7.12/1.50  fof(f52,plain,(
% 7.12/1.50    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f20])).
% 7.12/1.50  
% 7.12/1.50  fof(f1,axiom,(
% 7.12/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f13,plain,(
% 7.12/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.12/1.50    inference(pure_predicate_removal,[],[f1])).
% 7.12/1.50  
% 7.12/1.50  fof(f14,plain,(
% 7.12/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.12/1.50    inference(pure_predicate_removal,[],[f13])).
% 7.12/1.50  
% 7.12/1.50  fof(f15,plain,(
% 7.12/1.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 7.12/1.50    inference(ennf_transformation,[],[f14])).
% 7.12/1.50  
% 7.12/1.50  fof(f16,plain,(
% 7.12/1.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 7.12/1.50    inference(flattening,[],[f15])).
% 7.12/1.50  
% 7.12/1.50  fof(f48,plain,(
% 7.12/1.50    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f16])).
% 7.12/1.50  
% 7.12/1.50  fof(f71,plain,(
% 7.12/1.50    k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5)),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f2,axiom,(
% 7.12/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f17,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f2])).
% 7.12/1.50  
% 7.12/1.50  fof(f18,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f17])).
% 7.12/1.50  
% 7.12/1.50  fof(f51,plain,(
% 7.12/1.50    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f18])).
% 7.12/1.50  
% 7.12/1.50  fof(f59,plain,(
% 7.12/1.50    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f25])).
% 7.12/1.50  
% 7.12/1.50  fof(f47,plain,(
% 7.12/1.50    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f16])).
% 7.12/1.50  
% 7.12/1.50  fof(f72,plain,(
% 7.12/1.50    k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5)),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  fof(f7,axiom,(
% 7.12/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f26,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f7])).
% 7.12/1.50  
% 7.12/1.50  fof(f27,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f26])).
% 7.12/1.50  
% 7.12/1.50  fof(f60,plain,(
% 7.12/1.50    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f27])).
% 7.12/1.50  
% 7.12/1.50  fof(f49,plain,(
% 7.12/1.50    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f16])).
% 7.12/1.50  
% 7.12/1.50  fof(f9,axiom,(
% 7.12/1.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f30,plain,(
% 7.12/1.50    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f9])).
% 7.12/1.50  
% 7.12/1.50  fof(f31,plain,(
% 7.12/1.50    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f30])).
% 7.12/1.50  
% 7.12/1.50  fof(f62,plain,(
% 7.12/1.50    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f31])).
% 7.12/1.50  
% 7.12/1.50  fof(f50,plain,(
% 7.12/1.50    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f16])).
% 7.12/1.50  
% 7.12/1.50  fof(f5,axiom,(
% 7.12/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f23,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f5])).
% 7.12/1.50  
% 7.12/1.50  fof(f24,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f23])).
% 7.12/1.50  
% 7.12/1.50  fof(f57,plain,(
% 7.12/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f24])).
% 7.12/1.50  
% 7.12/1.50  fof(f8,axiom,(
% 7.12/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f28,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f8])).
% 7.12/1.50  
% 7.12/1.50  fof(f29,plain,(
% 7.12/1.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f28])).
% 7.12/1.50  
% 7.12/1.50  fof(f61,plain,(
% 7.12/1.50    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f29])).
% 7.12/1.50  
% 7.12/1.50  fof(f4,axiom,(
% 7.12/1.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 7.12/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.50  
% 7.12/1.50  fof(f21,plain,(
% 7.12/1.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.12/1.50    inference(ennf_transformation,[],[f4])).
% 7.12/1.50  
% 7.12/1.50  fof(f22,plain,(
% 7.12/1.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(flattening,[],[f21])).
% 7.12/1.50  
% 7.12/1.50  fof(f36,plain,(
% 7.12/1.50    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(nnf_transformation,[],[f22])).
% 7.12/1.50  
% 7.12/1.50  fof(f37,plain,(
% 7.12/1.50    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(rectify,[],[f36])).
% 7.12/1.50  
% 7.12/1.50  fof(f39,plain,(
% 7.12/1.50    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK1(X0))) != X1 & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 7.12/1.50    introduced(choice_axiom,[])).
% 7.12/1.50  
% 7.12/1.50  fof(f38,plain,(
% 7.12/1.50    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),X2)) != sK0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 7.12/1.50    introduced(choice_axiom,[])).
% 7.12/1.50  
% 7.12/1.50  fof(f40,plain,(
% 7.12/1.50    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),sK1(X0))) != sK0(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.12/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 7.12/1.50  
% 7.12/1.50  fof(f53,plain,(
% 7.12/1.50    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.12/1.50    inference(cnf_transformation,[],[f40])).
% 7.12/1.50  
% 7.12/1.50  fof(f73,plain,(
% 7.12/1.50    sK4 != sK5),
% 7.12/1.50    inference(cnf_transformation,[],[f45])).
% 7.12/1.50  
% 7.12/1.50  cnf(c_714,plain,
% 7.12/1.50      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 7.12/1.50      theory(equality) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_942,plain,
% 7.12/1.50      ( sK5 != X0_50 | sK4 != X0_50 | sK4 = sK5 ),
% 7.12/1.50      inference(instantiation,[status(thm)],[c_714]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_14657,plain,
% 7.12/1.50      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 7.12/1.50      inference(instantiation,[status(thm)],[c_942]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_21,negated_conjecture,
% 7.12/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.12/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_708,negated_conjecture,
% 7.12/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_909,plain,
% 7.12/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_22,negated_conjecture,
% 7.12/1.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 7.12/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_707,negated_conjecture,
% 7.12/1.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_910,plain,
% 7.12/1.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_23,negated_conjecture,
% 7.12/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.12/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_706,negated_conjecture,
% 7.12/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_911,plain,
% 7.12/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_17,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 7.12/1.50      | ~ v11_lattices(X1)
% 7.12/1.50      | ~ l3_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | ~ v10_lattices(X1)
% 7.12/1.50      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
% 7.12/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_25,negated_conjecture,
% 7.12/1.50      ( v11_lattices(sK2) ),
% 7.12/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_272,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 7.12/1.50      | ~ l3_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | ~ v10_lattices(X1)
% 7.12/1.50      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
% 7.12/1.50      | sK2 != X1 ),
% 7.12/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_273,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.12/1.50      | ~ l3_lattices(sK2)
% 7.12/1.50      | v2_struct_0(sK2)
% 7.12/1.50      | ~ v10_lattices(sK2)
% 7.12/1.50      | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
% 7.12/1.50      inference(unflattening,[status(thm)],[c_272]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_27,negated_conjecture,
% 7.12/1.50      ( ~ v2_struct_0(sK2) ),
% 7.12/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_26,negated_conjecture,
% 7.12/1.50      ( v10_lattices(sK2) ),
% 7.12/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_24,negated_conjecture,
% 7.12/1.50      ( l3_lattices(sK2) ),
% 7.12/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_277,plain,
% 7.12/1.50      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
% 7.12/1.50      inference(global_propositional_subsumption,
% 7.12/1.50                [status(thm)],
% 7.12/1.50                [c_273,c_27,c_26,c_24]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_278,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.12/1.50      | k4_lattices(sK2,k3_lattices(sK2,X2,X0),k3_lattices(sK2,X2,X1)) = k3_lattices(sK2,X2,k4_lattices(sK2,X0,X1)) ),
% 7.12/1.50      inference(renaming,[status(thm)],[c_277]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_705,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X2_50,u1_struct_0(sK2))
% 7.12/1.50      | k4_lattices(sK2,k3_lattices(sK2,X2_50,X0_50),k3_lattices(sK2,X2_50,X1_50)) = k3_lattices(sK2,X2_50,k4_lattices(sK2,X0_50,X1_50)) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_278]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_912,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,X0_50,X1_50),k3_lattices(sK2,X0_50,X2_50)) = k3_lattices(sK2,X0_50,k4_lattices(sK2,X1_50,X2_50))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X2_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1095,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,X0_50,X1_50),k3_lattices(sK2,X0_50,sK3)) = k3_lattices(sK2,X0_50,k4_lattices(sK2,X1_50,sK3))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_911,c_912]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_4711,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,sK4,X0_50),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK4,k4_lattices(sK2,X0_50,sK3))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_910,c_1095]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_6371,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK5),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK4,k4_lattices(sK2,sK5,sK3)) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_4711]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_13,plain,
% 7.12/1.50      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_6,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ l1_lattices(X1)
% 7.12/1.50      | ~ v6_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_359,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ v6_lattices(X1)
% 7.12/1.50      | ~ l3_lattices(X3)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | X1 != X3
% 7.12/1.50      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 7.12/1.50      inference(resolution_lifted,[status(thm)],[c_13,c_6]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_360,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ v6_lattices(X1)
% 7.12/1.50      | ~ l3_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 7.12/1.50      inference(unflattening,[status(thm)],[c_359]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_2,plain,
% 7.12/1.50      ( v6_lattices(X0)
% 7.12/1.50      | ~ l3_lattices(X0)
% 7.12/1.50      | v2_struct_0(X0)
% 7.12/1.50      | ~ v10_lattices(X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_408,plain,
% 7.12/1.50      ( v6_lattices(X0)
% 7.12/1.50      | ~ l3_lattices(X0)
% 7.12/1.50      | v2_struct_0(X0)
% 7.12/1.50      | sK2 != X0 ),
% 7.12/1.50      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_409,plain,
% 7.12/1.50      ( v6_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 7.12/1.50      inference(unflattening,[status(thm)],[c_408]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_79,plain,
% 7.12/1.50      ( v6_lattices(sK2)
% 7.12/1.50      | ~ l3_lattices(sK2)
% 7.12/1.50      | v2_struct_0(sK2)
% 7.12/1.50      | ~ v10_lattices(sK2) ),
% 7.12/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_411,plain,
% 7.12/1.50      ( v6_lattices(sK2) ),
% 7.12/1.50      inference(global_propositional_subsumption,
% 7.12/1.50                [status(thm)],
% 7.12/1.50                [c_409,c_27,c_26,c_24,c_79]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_457,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ l3_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 7.12/1.50      | sK2 != X1 ),
% 7.12/1.50      inference(resolution_lifted,[status(thm)],[c_360,c_411]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_458,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | ~ l3_lattices(sK2)
% 7.12/1.50      | v2_struct_0(sK2)
% 7.12/1.50      | k4_lattices(sK2,X0,X1) = k4_lattices(sK2,X1,X0) ),
% 7.12/1.50      inference(unflattening,[status(thm)],[c_457]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_462,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | k4_lattices(sK2,X0,X1) = k4_lattices(sK2,X1,X0) ),
% 7.12/1.50      inference(global_propositional_subsumption,
% 7.12/1.50                [status(thm)],
% 7.12/1.50                [c_458,c_27,c_24]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_703,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.50      | k4_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X1_50,X0_50) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_462]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_914,plain,
% 7.12/1.50      ( k4_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X1_50,X0_50)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1464,plain,
% 7.12/1.50      ( k4_lattices(sK2,X0_50,sK4) = k4_lattices(sK2,sK4,X0_50)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_910,c_914]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1910,plain,
% 7.12/1.50      ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK3,sK4) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_911,c_1464]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1463,plain,
% 7.12/1.50      ( k4_lattices(sK2,sK5,X0_50) = k4_lattices(sK2,X0_50,sK5)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_914]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1700,plain,
% 7.12/1.50      ( k4_lattices(sK2,sK5,sK3) = k4_lattices(sK2,sK3,sK5) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_911,c_1463]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_20,negated_conjecture,
% 7.12/1.50      ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
% 7.12/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_709,negated_conjecture,
% 7.12/1.50      ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_20]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1794,plain,
% 7.12/1.50      ( k4_lattices(sK2,sK5,sK3) = k4_lattices(sK2,sK3,sK4) ),
% 7.12/1.50      inference(demodulation,[status(thm)],[c_1700,c_709]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1911,plain,
% 7.12/1.50      ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK5,sK3) ),
% 7.12/1.50      inference(demodulation,[status(thm)],[c_1910,c_1794]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_4710,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),k3_lattices(sK2,sK5,sK3)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK3))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_1095]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_5,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ l2_lattices(X1)
% 7.12/1.50      | ~ v4_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_589,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ l2_lattices(X1)
% 7.12/1.50      | ~ v4_lattices(X1)
% 7.12/1.50      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 7.12/1.50      | sK2 != X1 ),
% 7.12/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_590,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | ~ l2_lattices(sK2)
% 7.12/1.50      | ~ v4_lattices(sK2)
% 7.12/1.50      | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
% 7.12/1.50      inference(unflattening,[status(thm)],[c_589]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_12,plain,
% 7.12/1.50      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_51,plain,
% 7.12/1.50      ( l2_lattices(sK2) | ~ l3_lattices(sK2) ),
% 7.12/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_3,plain,
% 7.12/1.50      ( v4_lattices(X0)
% 7.12/1.50      | ~ l3_lattices(X0)
% 7.12/1.50      | v2_struct_0(X0)
% 7.12/1.50      | ~ v10_lattices(X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_76,plain,
% 7.12/1.50      ( v4_lattices(sK2)
% 7.12/1.50      | ~ l3_lattices(sK2)
% 7.12/1.50      | v2_struct_0(sK2)
% 7.12/1.50      | ~ v10_lattices(sK2) ),
% 7.12/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_594,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
% 7.12/1.50      inference(global_propositional_subsumption,
% 7.12/1.50                [status(thm)],
% 7.12/1.50                [c_590,c_27,c_26,c_24,c_51,c_76]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_698,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.50      | k3_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X1_50,X0_50) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_594]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_919,plain,
% 7.12/1.50      ( k3_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X1_50,X0_50)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_3279,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK4,X0_50) = k3_lattices(sK2,X0_50,sK4)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_910,c_919]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_4824,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK3,sK4) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_911,c_3279]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_3278,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK5,X0_50) = k3_lattices(sK2,X0_50,sK5)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_919]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_3723,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK5) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_911,c_3278]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_19,negated_conjecture,
% 7.12/1.50      ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
% 7.12/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_710,negated_conjecture,
% 7.12/1.50      ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_19]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_3898,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK4) ),
% 7.12/1.50      inference(demodulation,[status(thm)],[c_3723,c_710]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_4830,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK5,sK3) ),
% 7.12/1.50      inference(demodulation,[status(thm)],[c_4824,c_3898]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_5850,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK3))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(light_normalisation,[status(thm)],[c_4710,c_4830]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_5855,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK4),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK5,k4_lattices(sK2,sK4,sK3)) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_910,c_5850]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_3722,plain,
% 7.12/1.50      ( k3_lattices(sK2,sK5,sK4) = k3_lattices(sK2,sK4,sK5) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_910,c_3278]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1093,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,X0_50,X1_50),k3_lattices(sK2,X0_50,sK5)) = k3_lattices(sK2,X0_50,k4_lattices(sK2,X1_50,sK5))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_912]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1123,plain,
% 7.12/1.50      ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),k3_lattices(sK2,sK5,sK5)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK5))
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_1093]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_14,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ l2_lattices(X1)
% 7.12/1.50      | ~ v4_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_547,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.50      | ~ l2_lattices(X1)
% 7.12/1.50      | ~ v4_lattices(X1)
% 7.12/1.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 7.12/1.50      | sK2 != X1 ),
% 7.12/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_548,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | ~ l2_lattices(sK2)
% 7.12/1.50      | ~ v4_lattices(sK2)
% 7.12/1.50      | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
% 7.12/1.50      inference(unflattening,[status(thm)],[c_547]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_552,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.50      | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
% 7.12/1.50      inference(global_propositional_subsumption,
% 7.12/1.50                [status(thm)],
% 7.12/1.50                [c_548,c_27,c_26,c_24,c_51,c_76]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_700,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.50      | k1_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X0_50,X1_50) ),
% 7.12/1.50      inference(subtyping,[status(esa)],[c_552]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_917,plain,
% 7.12/1.50      ( k1_lattices(sK2,X0_50,X1_50) = k3_lattices(sK2,X0_50,X1_50)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.50      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_2249,plain,
% 7.12/1.50      ( k1_lattices(sK2,sK5,X0_50) = k3_lattices(sK2,sK5,X0_50)
% 7.12/1.50      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_917]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_2362,plain,
% 7.12/1.50      ( k1_lattices(sK2,sK5,sK5) = k3_lattices(sK2,sK5,sK5) ),
% 7.12/1.50      inference(superposition,[status(thm)],[c_909,c_2249]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_1,plain,
% 7.12/1.50      ( v8_lattices(X0)
% 7.12/1.50      | ~ l3_lattices(X0)
% 7.12/1.50      | v2_struct_0(X0)
% 7.12/1.50      | ~ v10_lattices(X0) ),
% 7.12/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_16,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ v6_lattices(X1)
% 7.12/1.50      | ~ v8_lattices(X1)
% 7.12/1.50      | ~ l3_lattices(X1)
% 7.12/1.50      | v2_struct_0(X1)
% 7.12/1.50      | ~ v9_lattices(X1)
% 7.12/1.50      | k1_lattices(X1,X0,X0) = X0 ),
% 7.12/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.12/1.50  
% 7.12/1.50  cnf(c_301,plain,
% 7.12/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.50      | ~ v6_lattices(X1)
% 7.12/1.50      | ~ l3_lattices(X2)
% 7.12/1.50      | ~ l3_lattices(X1)
% 7.12/1.50      | v2_struct_0(X2)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | ~ v10_lattices(X2)
% 7.12/1.51      | ~ v9_lattices(X1)
% 7.12/1.51      | X1 != X2
% 7.12/1.51      | k1_lattices(X1,X0,X0) = X0 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_302,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ v6_lattices(X1)
% 7.12/1.51      | ~ l3_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | ~ v10_lattices(X1)
% 7.12/1.51      | ~ v9_lattices(X1)
% 7.12/1.51      | k1_lattices(X1,X0,X0) = X0 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_301]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_0,plain,
% 7.12/1.51      ( ~ l3_lattices(X0)
% 7.12/1.51      | v2_struct_0(X0)
% 7.12/1.51      | ~ v10_lattices(X0)
% 7.12/1.51      | v9_lattices(X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_320,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ l3_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | ~ v10_lattices(X1)
% 7.12/1.51      | k1_lattices(X1,X0,X0) = X0 ),
% 7.12/1.51      inference(forward_subsumption_resolution,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_302,c_0,c_2]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_430,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ l3_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | k1_lattices(X1,X0,X0) = X0
% 7.12/1.51      | sK2 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_320,c_26]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_431,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ l3_lattices(sK2)
% 7.12/1.51      | v2_struct_0(sK2)
% 7.12/1.51      | k1_lattices(sK2,X0,X0) = X0 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_430]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_435,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | k1_lattices(sK2,X0,X0) = X0 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_431,c_27,c_24]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_704,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.51      | k1_lattices(sK2,X0_50,X0_50) = X0_50 ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_435]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_913,plain,
% 7.12/1.51      ( k1_lattices(sK2,X0_50,X0_50) = X0_50
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1053,plain,
% 7.12/1.51      ( k1_lattices(sK2,sK5,sK5) = sK5 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_909,c_913]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2365,plain,
% 7.12/1.51      ( k3_lattices(sK2,sK5,sK5) = sK5 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_2362,c_1053]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5530,plain,
% 7.12/1.51      ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_50),sK5) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_50,sK5))
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_1123,c_2365]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5536,plain,
% 7.12/1.51      ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),sK5) = k3_lattices(sK2,sK5,k4_lattices(sK2,sK3,sK5)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_911,c_5530]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1969,plain,
% 7.12/1.51      ( k4_lattices(sK2,sK4,sK3) = k4_lattices(sK2,sK3,sK5) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_1911,c_1700]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_11,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 7.12/1.51      | ~ l2_lattices(X1)
% 7.12/1.51      | ~ v4_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_568,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 7.12/1.51      | ~ l2_lattices(X1)
% 7.12/1.51      | ~ v4_lattices(X1)
% 7.12/1.51      | sK2 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_569,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.51      | m1_subset_1(k3_lattices(sK2,X0,X1),u1_struct_0(sK2))
% 7.12/1.51      | ~ l2_lattices(sK2)
% 7.12/1.51      | ~ v4_lattices(sK2) ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_568]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_573,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.51      | m1_subset_1(k3_lattices(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_569,c_27,c_26,c_24,c_51,c_76]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_699,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.51      | m1_subset_1(k3_lattices(sK2,X0_50,X1_50),u1_struct_0(sK2)) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_573]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_918,plain,
% 7.12/1.51      ( m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.51      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.51      | m1_subset_1(k3_lattices(sK2,X0_50,X1_50),u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2519,plain,
% 7.12/1.51      ( m1_subset_1(k3_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 7.12/1.51      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 7.12/1.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_710,c_918]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_32,plain,
% 7.12/1.51      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_34,plain,
% 7.12/1.51      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2683,plain,
% 7.12/1.51      ( m1_subset_1(k3_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_2519,c_32,c_34]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2695,plain,
% 7.12/1.51      ( k4_lattices(sK2,k3_lattices(sK2,sK3,sK4),sK5) = k4_lattices(sK2,sK5,k3_lattices(sK2,sK3,sK4)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_2683,c_1463]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4076,plain,
% 7.12/1.51      ( k4_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),sK5) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_3898,c_2695]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_15,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | ~ l1_lattices(X1)
% 7.12/1.51      | ~ v6_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_335,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | ~ v6_lattices(X1)
% 7.12/1.51      | ~ l3_lattices(X3)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | X1 != X3
% 7.12/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_336,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | ~ v6_lattices(X1)
% 7.12/1.51      | ~ l3_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_335]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_478,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | ~ l3_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 7.12/1.51      | sK2 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_336,c_411]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_479,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.51      | ~ l3_lattices(sK2)
% 7.12/1.51      | v2_struct_0(sK2)
% 7.12/1.51      | k2_lattices(sK2,X0,X1) = k4_lattices(sK2,X0,X1) ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_478]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_483,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.51      | k2_lattices(sK2,X0,X1) = k4_lattices(sK2,X0,X1) ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_479,c_27,c_24]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_702,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.51      | k2_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X0_50,X1_50) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_483]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_915,plain,
% 7.12/1.51      ( k2_lattices(sK2,X0_50,X1_50) = k4_lattices(sK2,X0_50,X1_50)
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.51      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1959,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK5,X0_50) = k4_lattices(sK2,sK5,X0_50)
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_909,c_915]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2691,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK5,k3_lattices(sK2,sK3,sK4)) = k4_lattices(sK2,sK5,k3_lattices(sK2,sK3,sK4)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_2683,c_1959]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4082,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = k4_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_3898,c_2691]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2364,plain,
% 7.12/1.51      ( k1_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK5,sK3) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_911,c_2249]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_10,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | ~ l3_lattices(X1)
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | ~ v9_lattices(X1)
% 7.12/1.51      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 7.12/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_520,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.12/1.51      | v2_struct_0(X1)
% 7.12/1.51      | ~ v9_lattices(X1)
% 7.12/1.51      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 7.12/1.51      | sK2 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_521,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.51      | v2_struct_0(sK2)
% 7.12/1.51      | ~ v9_lattices(sK2)
% 7.12/1.51      | k2_lattices(sK2,X0,k1_lattices(sK2,X0,X1)) = X0 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_520]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_85,plain,
% 7.12/1.51      ( ~ l3_lattices(sK2)
% 7.12/1.51      | v2_struct_0(sK2)
% 7.12/1.51      | ~ v10_lattices(sK2)
% 7.12/1.51      | v9_lattices(sK2) ),
% 7.12/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_525,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.12/1.51      | k2_lattices(sK2,X0,k1_lattices(sK2,X0,X1)) = X0 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_521,c_27,c_26,c_24,c_85]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_701,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK2))
% 7.12/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK2))
% 7.12/1.51      | k2_lattices(sK2,X0_50,k1_lattices(sK2,X0_50,X1_50)) = X0_50 ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_525]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_916,plain,
% 7.12/1.51      ( k2_lattices(sK2,X0_50,k1_lattices(sK2,X0_50,X1_50)) = X0_50
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 7.12/1.51      | m1_subset_1(X1_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1321,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK5,k1_lattices(sK2,sK5,X0_50)) = sK5
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_909,c_916]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1431,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK5,k1_lattices(sK2,sK5,sK3)) = sK5 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_911,c_1321]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2517,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = sK5 ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_2364,c_1431]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4091,plain,
% 7.12/1.51      ( k4_lattices(sK2,sK5,k3_lattices(sK2,sK5,sK3)) = sK5 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_4082,c_2517]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4093,plain,
% 7.12/1.51      ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),sK5) = sK5 ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_4076,c_4091]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5538,plain,
% 7.12/1.51      ( k3_lattices(sK2,sK5,k4_lattices(sK2,sK4,sK3)) = sK5 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_5536,c_1969,c_4093]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5859,plain,
% 7.12/1.51      ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK5),k3_lattices(sK2,sK4,sK3)) = sK5 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_5855,c_3722,c_5538]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6377,plain,
% 7.12/1.51      ( k3_lattices(sK2,sK4,k4_lattices(sK2,sK4,sK3)) = sK5 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_6371,c_1911,c_5859]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6372,plain,
% 7.12/1.51      ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK4),k3_lattices(sK2,sK4,sK3)) = k3_lattices(sK2,sK4,k4_lattices(sK2,sK4,sK3)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_910,c_4711]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2250,plain,
% 7.12/1.51      ( k1_lattices(sK2,sK4,X0_50) = k3_lattices(sK2,sK4,X0_50)
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_910,c_917]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2727,plain,
% 7.12/1.51      ( k1_lattices(sK2,sK4,sK4) = k3_lattices(sK2,sK4,sK4) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_910,c_2250]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1054,plain,
% 7.12/1.51      ( k1_lattices(sK2,sK4,sK4) = sK4 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_910,c_913]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2731,plain,
% 7.12/1.51      ( k3_lattices(sK2,sK4,sK4) = sK4 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_2727,c_1054]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1960,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,X0_50) = k4_lattices(sK2,sK4,X0_50)
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_910,c_915]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2690,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK3,sK4)) = k4_lattices(sK2,sK4,k3_lattices(sK2,sK3,sK4)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_2683,c_1960]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4083,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK5,sK3)) = k4_lattices(sK2,sK4,k3_lattices(sK2,sK5,sK3)) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_3898,c_2690]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4895,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) = k4_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_4830,c_4083]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2728,plain,
% 7.12/1.51      ( k1_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK4,sK3) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_911,c_2250]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1322,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,k1_lattices(sK2,sK4,X0_50)) = sK4
% 7.12/1.51      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_910,c_916]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1511,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,k1_lattices(sK2,sK4,sK3)) = sK4 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_911,c_1322]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2811,plain,
% 7.12/1.51      ( k2_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) = sK4 ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_2728,c_1511]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4907,plain,
% 7.12/1.51      ( k4_lattices(sK2,sK4,k3_lattices(sK2,sK4,sK3)) = sK4 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_4895,c_2811]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6376,plain,
% 7.12/1.51      ( k3_lattices(sK2,sK4,k4_lattices(sK2,sK4,sK3)) = sK4 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_6372,c_2731,c_4907]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_10653,plain,
% 7.12/1.51      ( sK5 = sK4 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_6377,c_6376]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_713,plain,( X0_50 = X0_50 ),theory(equality) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1120,plain,
% 7.12/1.51      ( sK4 = sK4 ),
% 7.12/1.51      inference(instantiation,[status(thm)],[c_713]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_18,negated_conjecture,
% 7.12/1.51      ( sK4 != sK5 ),
% 7.12/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_711,negated_conjecture,
% 7.12/1.51      ( sK4 != sK5 ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_18]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(contradiction,plain,
% 7.12/1.51      ( $false ),
% 7.12/1.51      inference(minisat,[status(thm)],[c_14657,c_10653,c_1120,c_711]) ).
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  ------                               Statistics
% 7.12/1.51  
% 7.12/1.51  ------ General
% 7.12/1.51  
% 7.12/1.51  abstr_ref_over_cycles:                  0
% 7.12/1.51  abstr_ref_under_cycles:                 0
% 7.12/1.51  gc_basic_clause_elim:                   0
% 7.12/1.51  forced_gc_time:                         0
% 7.12/1.51  parsing_time:                           0.018
% 7.12/1.51  unif_index_cands_time:                  0.
% 7.12/1.51  unif_index_add_time:                    0.
% 7.12/1.51  orderings_time:                         0.
% 7.12/1.51  out_proof_time:                         0.013
% 7.12/1.51  total_time:                             0.587
% 7.12/1.51  num_of_symbols:                         53
% 7.12/1.51  num_of_terms:                           14777
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing
% 7.12/1.51  
% 7.12/1.51  num_of_splits:                          0
% 7.12/1.51  num_of_split_atoms:                     0
% 7.12/1.51  num_of_reused_defs:                     0
% 7.12/1.51  num_eq_ax_congr_red:                    22
% 7.12/1.51  num_of_sem_filtered_clauses:            1
% 7.12/1.51  num_of_subtypes:                        3
% 7.12/1.51  monotx_restored_types:                  0
% 7.12/1.51  sat_num_of_epr_types:                   0
% 7.12/1.51  sat_num_of_non_cyclic_types:            0
% 7.12/1.51  sat_guarded_non_collapsed_types:        1
% 7.12/1.51  num_pure_diseq_elim:                    0
% 7.12/1.51  simp_replaced_by:                       0
% 7.12/1.51  res_preprocessed:                       82
% 7.12/1.51  prep_upred:                             0
% 7.12/1.51  prep_unflattend:                        18
% 7.12/1.51  smt_new_axioms:                         0
% 7.12/1.51  pred_elim_cands:                        1
% 7.12/1.51  pred_elim:                              10
% 7.12/1.51  pred_elim_cl:                           13
% 7.12/1.51  pred_elim_cycles:                       12
% 7.12/1.51  merged_defs:                            0
% 7.12/1.51  merged_defs_ncl:                        0
% 7.12/1.51  bin_hyper_res:                          0
% 7.12/1.51  prep_cycles:                            4
% 7.12/1.51  pred_elim_time:                         0.009
% 7.12/1.51  splitting_time:                         0.
% 7.12/1.51  sem_filter_time:                        0.
% 7.12/1.51  monotx_time:                            0.
% 7.12/1.51  subtype_inf_time:                       0.
% 7.12/1.51  
% 7.12/1.51  ------ Problem properties
% 7.12/1.51  
% 7.12/1.51  clauses:                                14
% 7.12/1.51  conjectures:                            6
% 7.12/1.51  epr:                                    1
% 7.12/1.51  horn:                                   14
% 7.12/1.51  ground:                                 6
% 7.12/1.51  unary:                                  6
% 7.12/1.51  binary:                                 1
% 7.12/1.51  lits:                                   30
% 7.12/1.51  lits_eq:                                10
% 7.12/1.51  fd_pure:                                0
% 7.12/1.51  fd_pseudo:                              0
% 7.12/1.51  fd_cond:                                0
% 7.12/1.51  fd_pseudo_cond:                         0
% 7.12/1.51  ac_symbols:                             0
% 7.12/1.51  
% 7.12/1.51  ------ Propositional Solver
% 7.12/1.51  
% 7.12/1.51  prop_solver_calls:                      37
% 7.12/1.51  prop_fast_solver_calls:                 967
% 7.12/1.51  smt_solver_calls:                       0
% 7.12/1.51  smt_fast_solver_calls:                  0
% 7.12/1.51  prop_num_of_clauses:                    7426
% 7.12/1.51  prop_preprocess_simplified:             13037
% 7.12/1.51  prop_fo_subsumed:                       25
% 7.12/1.51  prop_solver_time:                       0.
% 7.12/1.51  smt_solver_time:                        0.
% 7.12/1.51  smt_fast_solver_time:                   0.
% 7.12/1.51  prop_fast_solver_time:                  0.
% 7.12/1.51  prop_unsat_core_time:                   0.001
% 7.12/1.51  
% 7.12/1.51  ------ QBF
% 7.12/1.51  
% 7.12/1.51  qbf_q_res:                              0
% 7.12/1.51  qbf_num_tautologies:                    0
% 7.12/1.51  qbf_prep_cycles:                        0
% 7.12/1.51  
% 7.12/1.51  ------ BMC1
% 7.12/1.51  
% 7.12/1.51  bmc1_current_bound:                     -1
% 7.12/1.51  bmc1_last_solved_bound:                 -1
% 7.12/1.51  bmc1_unsat_core_size:                   -1
% 7.12/1.51  bmc1_unsat_core_parents_size:           -1
% 7.12/1.51  bmc1_merge_next_fun:                    0
% 7.12/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation
% 7.12/1.51  
% 7.12/1.51  inst_num_of_clauses:                    3342
% 7.12/1.51  inst_num_in_passive:                    1295
% 7.12/1.51  inst_num_in_active:                     871
% 7.12/1.51  inst_num_in_unprocessed:                1175
% 7.12/1.51  inst_num_of_loops:                      1091
% 7.12/1.51  inst_num_of_learning_restarts:          0
% 7.12/1.51  inst_num_moves_active_passive:          210
% 7.12/1.51  inst_lit_activity:                      0
% 7.12/1.51  inst_lit_activity_moves:                2
% 7.12/1.51  inst_num_tautologies:                   0
% 7.12/1.51  inst_num_prop_implied:                  0
% 7.12/1.51  inst_num_existing_simplified:           0
% 7.12/1.51  inst_num_eq_res_simplified:             0
% 7.12/1.51  inst_num_child_elim:                    0
% 7.12/1.51  inst_num_of_dismatching_blockings:      1574
% 7.12/1.51  inst_num_of_non_proper_insts:           3877
% 7.12/1.51  inst_num_of_duplicates:                 0
% 7.12/1.51  inst_inst_num_from_inst_to_res:         0
% 7.12/1.51  inst_dismatching_checking_time:         0.
% 7.12/1.51  
% 7.12/1.51  ------ Resolution
% 7.12/1.51  
% 7.12/1.51  res_num_of_clauses:                     0
% 7.12/1.51  res_num_in_passive:                     0
% 7.12/1.51  res_num_in_active:                      0
% 7.12/1.51  res_num_of_loops:                       86
% 7.12/1.51  res_forward_subset_subsumed:            119
% 7.12/1.51  res_backward_subset_subsumed:           0
% 7.12/1.51  res_forward_subsumed:                   0
% 7.12/1.51  res_backward_subsumed:                  0
% 7.12/1.51  res_forward_subsumption_resolution:     2
% 7.12/1.51  res_backward_subsumption_resolution:    0
% 7.12/1.51  res_clause_to_clause_subsumption:       1222
% 7.12/1.51  res_orphan_elimination:                 0
% 7.12/1.51  res_tautology_del:                      318
% 7.12/1.51  res_num_eq_res_simplified:              0
% 7.12/1.51  res_num_sel_changes:                    0
% 7.12/1.51  res_moves_from_active_to_pass:          0
% 7.12/1.51  
% 7.12/1.51  ------ Superposition
% 7.12/1.51  
% 7.12/1.51  sup_time_total:                         0.
% 7.12/1.51  sup_time_generating:                    0.
% 7.12/1.51  sup_time_sim_full:                      0.
% 7.12/1.51  sup_time_sim_immed:                     0.
% 7.12/1.51  
% 7.12/1.51  sup_num_of_clauses:                     328
% 7.12/1.51  sup_num_in_active:                      160
% 7.12/1.51  sup_num_in_passive:                     168
% 7.12/1.51  sup_num_of_loops:                       218
% 7.12/1.51  sup_fw_superposition:                   390
% 7.12/1.51  sup_bw_superposition:                   123
% 7.12/1.51  sup_immediate_simplified:               214
% 7.12/1.51  sup_given_eliminated:                   1
% 7.12/1.51  comparisons_done:                       0
% 7.12/1.51  comparisons_avoided:                    0
% 7.12/1.51  
% 7.12/1.51  ------ Simplifications
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  sim_fw_subset_subsumed:                 11
% 7.12/1.51  sim_bw_subset_subsumed:                 0
% 7.12/1.51  sim_fw_subsumed:                        6
% 7.12/1.51  sim_bw_subsumed:                        0
% 7.12/1.51  sim_fw_subsumption_res:                 0
% 7.12/1.51  sim_bw_subsumption_res:                 0
% 7.12/1.51  sim_tautology_del:                      0
% 7.12/1.51  sim_eq_tautology_del:                   132
% 7.12/1.51  sim_eq_res_simp:                        0
% 7.12/1.51  sim_fw_demodulated:                     10
% 7.12/1.51  sim_bw_demodulated:                     65
% 7.12/1.51  sim_light_normalised:                   257
% 7.12/1.51  sim_joinable_taut:                      0
% 7.12/1.51  sim_joinable_simp:                      0
% 7.12/1.51  sim_ac_normalised:                      0
% 7.12/1.51  sim_smt_subsumption:                    0
% 7.12/1.51  
%------------------------------------------------------------------------------

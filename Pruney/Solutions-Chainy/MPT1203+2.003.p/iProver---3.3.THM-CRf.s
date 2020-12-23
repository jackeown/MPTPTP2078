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
% DateTime   : Thu Dec  3 12:13:14 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  193 (4256 expanded)
%              Number of clauses        :  132 ( 947 expanded)
%              Number of leaves         :   14 (1448 expanded)
%              Depth                    :   27
%              Number of atoms          :  736 (33267 expanded)
%              Number of equality atoms :  206 (10954 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK3 != X2
        & k3_lattices(X0,X1,sK3) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK3) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK2 != X3
            & k3_lattices(X0,X1,sK2) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK2) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                & k3_lattices(X0,sK1,X2) = k3_lattices(X0,sK1,X3)
                & k4_lattices(X0,sK1,X2) = k4_lattices(X0,sK1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
                  & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3)
                  & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v11_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( sK2 != sK3
    & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
    & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v11_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f38,f37,f36,f35])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f49,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f43,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_612,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_783,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_614,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_781,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_324,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_325,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_66,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_327,plain,
    ( v6_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_23,c_22,c_20,c_66])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_327])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_10,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_41,plain,
    ( l1_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_23,c_20,c_41])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0_47,X1_47),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_366])).

cnf(c_785,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k4_lattices(sK0,X0_47,X1_47),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_313,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_22])).

cnf(c_314,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_63,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_316,plain,
    ( v4_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_23,c_22,c_20,c_63])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_316])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_9,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_44,plain,
    ( l2_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_23,c_20,c_44])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | k1_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_787,plain,
    ( k1_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2189,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),X2_47) = k3_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),X2_47)
    | m1_subset_1(X2_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_787])).

cnf(c_27192,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK3) = k3_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK3)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_2189])).

cnf(c_28278,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK3)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_27192])).

cnf(c_28552,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK3) ),
    inference(superposition,[status(thm)],[c_783,c_28278])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_613,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_782,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_327])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_23,c_20,c_41])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | k4_lattices(sK0,X0_47,X1_47) = k4_lattices(sK0,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_786,plain,
    ( k4_lattices(sK0,X0_47,X1_47) = k4_lattices(sK0,X1_47,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_1501,plain,
    ( k4_lattices(sK0,X0_47,sK2) = k4_lattices(sK0,sK2,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_786])).

cnf(c_1867,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_783,c_1501])).

cnf(c_1500,plain,
    ( k4_lattices(sK0,X0_47,sK3) = k4_lattices(sK0,sK3,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_786])).

cnf(c_1521,plain,
    ( k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_783,c_1500])).

cnf(c_16,negated_conjecture,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_615,negated_conjecture,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1647,plain,
    ( k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1521,c_615])).

cnf(c_1873,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_1867,c_1647])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v8_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v8_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_256,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_1])).

cnf(c_261,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_292,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_22])).

cnf(c_293,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_297,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_23,c_20])).

cnf(c_298,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_7,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_461,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_462,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_20,c_44])).

cnf(c_467,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_466])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | X0 != X2
    | k1_lattices(sK0,X1,X0) = X0
    | k4_lattices(sK0,X2,X3) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_298,c_467])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,X1,X0),u1_struct_0(sK0))
    | k1_lattices(sK0,k4_lattices(sK0,X1,X0),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,k4_lattices(sK0,X1,X0),X1) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_521,c_366])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | k1_lattices(sK0,k4_lattices(sK0,X1_47,X0_47),X1_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_533])).

cnf(c_789,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),X0_47) = X0_47
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_3722,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK3) = sK3
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_789])).

cnf(c_3739,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_783,c_3722])).

cnf(c_3741,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3739,c_1873])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X0)) = k3_lattices(sK0,X1,k4_lattices(sK0,X2,X0)) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X0)) = k3_lattices(sK0,X1,k4_lattices(sK0,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_23,c_22,c_20])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k4_lattices(sK0,k3_lattices(sK0,X2,X0),k3_lattices(sK0,X2,X1)) = k3_lattices(sK0,X2,k4_lattices(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK0))
    | k4_lattices(sK0,k3_lattices(sK0,X2_47,X0_47),k3_lattices(sK0,X2_47,X1_47)) = k3_lattices(sK0,X2_47,k4_lattices(sK0,X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_784,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,X0_47,X1_47),k3_lattices(sK0,X0_47,X2_47)) = k3_lattices(sK0,X0_47,k4_lattices(sK0,X1_47,X2_47))
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_936,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,X0_47,X1_47),k3_lattices(sK0,X0_47,sK2)) = k3_lattices(sK0,X0_47,k4_lattices(sK0,X1_47,sK2))
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_784])).

cnf(c_4553,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,X0_47),k3_lattices(sK0,sK3,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,X0_47,sK2))
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_936])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_316])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_23,c_20,c_44])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | k3_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_437])).

cnf(c_788,plain,
    ( k3_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X1_47,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_2952,plain,
    ( k3_lattices(sK0,sK3,X0_47) = k3_lattices(sK0,X0_47,sK3)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_788])).

cnf(c_3071,plain,
    ( k3_lattices(sK0,sK3,sK2) = k3_lattices(sK0,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_782,c_2952])).

cnf(c_4558,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,X0_47),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,X0_47,sK2))
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4553,c_3071])).

cnf(c_21692,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_783,c_4558])).

cnf(c_2953,plain,
    ( k3_lattices(sK0,sK2,X0_47) = k3_lattices(sK0,X0_47,sK2)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_788])).

cnf(c_3356,plain,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_783,c_2953])).

cnf(c_3072,plain,
    ( k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_783,c_2952])).

cnf(c_15,negated_conjecture,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_616,negated_conjecture,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3159,plain,
    ( k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3072,c_616])).

cnf(c_3361,plain,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_3356,c_3159])).

cnf(c_935,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,X0_47,X1_47),k3_lattices(sK0,X0_47,sK3)) = k3_lattices(sK0,X0_47,k4_lattices(sK0,X1_47,sK3))
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_784])).

cnf(c_947,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,X0_47),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,X0_47,sK3))
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_935])).

cnf(c_4797,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_783,c_947])).

cnf(c_1957,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_1873,c_1521])).

cnf(c_4799,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4797,c_1957])).

cnf(c_21703,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_21692,c_1867,c_3361,c_4799])).

cnf(c_1010,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_785])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1021,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_28,c_30])).

cnf(c_1746,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1647,c_1021])).

cnf(c_1956,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1873,c_1746])).

cnf(c_11241,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1956,c_2952])).

cnf(c_22085,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK3) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_21703,c_11241])).

cnf(c_28562,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_28552,c_1873,c_3741,c_22085])).

cnf(c_27193,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK2) = k3_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK2)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_2189])).

cnf(c_29498,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK2)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_27193])).

cnf(c_30169,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_783,c_29498])).

cnf(c_3723,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,X0_47),sK2) = sK2
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_789])).

cnf(c_3855,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_783,c_3723])).

cnf(c_11240,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1956,c_2953])).

cnf(c_30178,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_30169,c_1873,c_3855,c_11240])).

cnf(c_33067,plain,
    ( sK3 = sK2 ),
    inference(light_normalisation,[status(thm)],[c_28562,c_30178])).

cnf(c_14,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_617,negated_conjecture,
    ( sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_33217,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_33067,c_617])).

cnf(c_33218,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_33217])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.66/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.66/2.00  
% 11.66/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.66/2.00  
% 11.66/2.00  ------  iProver source info
% 11.66/2.00  
% 11.66/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.66/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.66/2.00  git: non_committed_changes: false
% 11.66/2.00  git: last_make_outside_of_git: false
% 11.66/2.00  
% 11.66/2.00  ------ 
% 11.66/2.00  
% 11.66/2.00  ------ Input Options
% 11.66/2.00  
% 11.66/2.00  --out_options                           all
% 11.66/2.00  --tptp_safe_out                         true
% 11.66/2.00  --problem_path                          ""
% 11.66/2.00  --include_path                          ""
% 11.66/2.00  --clausifier                            res/vclausify_rel
% 11.66/2.00  --clausifier_options                    ""
% 11.66/2.00  --stdin                                 false
% 11.66/2.00  --stats_out                             all
% 11.66/2.00  
% 11.66/2.00  ------ General Options
% 11.66/2.00  
% 11.66/2.00  --fof                                   false
% 11.66/2.00  --time_out_real                         305.
% 11.66/2.00  --time_out_virtual                      -1.
% 11.66/2.00  --symbol_type_check                     false
% 11.66/2.00  --clausify_out                          false
% 11.66/2.00  --sig_cnt_out                           false
% 11.66/2.00  --trig_cnt_out                          false
% 11.66/2.00  --trig_cnt_out_tolerance                1.
% 11.66/2.00  --trig_cnt_out_sk_spl                   false
% 11.66/2.00  --abstr_cl_out                          false
% 11.66/2.00  
% 11.66/2.00  ------ Global Options
% 11.66/2.00  
% 11.66/2.00  --schedule                              default
% 11.66/2.00  --add_important_lit                     false
% 11.66/2.00  --prop_solver_per_cl                    1000
% 11.66/2.00  --min_unsat_core                        false
% 11.66/2.00  --soft_assumptions                      false
% 11.66/2.00  --soft_lemma_size                       3
% 11.66/2.00  --prop_impl_unit_size                   0
% 11.66/2.00  --prop_impl_unit                        []
% 11.66/2.00  --share_sel_clauses                     true
% 11.66/2.00  --reset_solvers                         false
% 11.66/2.00  --bc_imp_inh                            [conj_cone]
% 11.66/2.00  --conj_cone_tolerance                   3.
% 11.66/2.00  --extra_neg_conj                        none
% 11.66/2.00  --large_theory_mode                     true
% 11.66/2.00  --prolific_symb_bound                   200
% 11.66/2.00  --lt_threshold                          2000
% 11.66/2.00  --clause_weak_htbl                      true
% 11.66/2.00  --gc_record_bc_elim                     false
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing Options
% 11.66/2.00  
% 11.66/2.00  --preprocessing_flag                    true
% 11.66/2.00  --time_out_prep_mult                    0.1
% 11.66/2.00  --splitting_mode                        input
% 11.66/2.00  --splitting_grd                         true
% 11.66/2.00  --splitting_cvd                         false
% 11.66/2.00  --splitting_cvd_svl                     false
% 11.66/2.00  --splitting_nvd                         32
% 11.66/2.00  --sub_typing                            true
% 11.66/2.00  --prep_gs_sim                           true
% 11.66/2.00  --prep_unflatten                        true
% 11.66/2.00  --prep_res_sim                          true
% 11.66/2.00  --prep_upred                            true
% 11.66/2.00  --prep_sem_filter                       exhaustive
% 11.66/2.00  --prep_sem_filter_out                   false
% 11.66/2.00  --pred_elim                             true
% 11.66/2.00  --res_sim_input                         true
% 11.66/2.00  --eq_ax_congr_red                       true
% 11.66/2.00  --pure_diseq_elim                       true
% 11.66/2.00  --brand_transform                       false
% 11.66/2.00  --non_eq_to_eq                          false
% 11.66/2.00  --prep_def_merge                        true
% 11.66/2.00  --prep_def_merge_prop_impl              false
% 11.66/2.00  --prep_def_merge_mbd                    true
% 11.66/2.00  --prep_def_merge_tr_red                 false
% 11.66/2.00  --prep_def_merge_tr_cl                  false
% 11.66/2.00  --smt_preprocessing                     true
% 11.66/2.00  --smt_ac_axioms                         fast
% 11.66/2.00  --preprocessed_out                      false
% 11.66/2.00  --preprocessed_stats                    false
% 11.66/2.00  
% 11.66/2.00  ------ Abstraction refinement Options
% 11.66/2.00  
% 11.66/2.00  --abstr_ref                             []
% 11.66/2.00  --abstr_ref_prep                        false
% 11.66/2.00  --abstr_ref_until_sat                   false
% 11.66/2.00  --abstr_ref_sig_restrict                funpre
% 11.66/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.66/2.00  --abstr_ref_under                       []
% 11.66/2.00  
% 11.66/2.00  ------ SAT Options
% 11.66/2.00  
% 11.66/2.00  --sat_mode                              false
% 11.66/2.00  --sat_fm_restart_options                ""
% 11.66/2.00  --sat_gr_def                            false
% 11.66/2.00  --sat_epr_types                         true
% 11.66/2.00  --sat_non_cyclic_types                  false
% 11.66/2.00  --sat_finite_models                     false
% 11.66/2.00  --sat_fm_lemmas                         false
% 11.66/2.00  --sat_fm_prep                           false
% 11.66/2.00  --sat_fm_uc_incr                        true
% 11.66/2.00  --sat_out_model                         small
% 11.66/2.00  --sat_out_clauses                       false
% 11.66/2.00  
% 11.66/2.00  ------ QBF Options
% 11.66/2.00  
% 11.66/2.00  --qbf_mode                              false
% 11.66/2.00  --qbf_elim_univ                         false
% 11.66/2.00  --qbf_dom_inst                          none
% 11.66/2.00  --qbf_dom_pre_inst                      false
% 11.66/2.00  --qbf_sk_in                             false
% 11.66/2.00  --qbf_pred_elim                         true
% 11.66/2.00  --qbf_split                             512
% 11.66/2.00  
% 11.66/2.00  ------ BMC1 Options
% 11.66/2.00  
% 11.66/2.00  --bmc1_incremental                      false
% 11.66/2.00  --bmc1_axioms                           reachable_all
% 11.66/2.00  --bmc1_min_bound                        0
% 11.66/2.00  --bmc1_max_bound                        -1
% 11.66/2.00  --bmc1_max_bound_default                -1
% 11.66/2.00  --bmc1_symbol_reachability              true
% 11.66/2.00  --bmc1_property_lemmas                  false
% 11.66/2.00  --bmc1_k_induction                      false
% 11.66/2.00  --bmc1_non_equiv_states                 false
% 11.66/2.00  --bmc1_deadlock                         false
% 11.66/2.00  --bmc1_ucm                              false
% 11.66/2.00  --bmc1_add_unsat_core                   none
% 11.66/2.00  --bmc1_unsat_core_children              false
% 11.66/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.66/2.00  --bmc1_out_stat                         full
% 11.66/2.00  --bmc1_ground_init                      false
% 11.66/2.00  --bmc1_pre_inst_next_state              false
% 11.66/2.00  --bmc1_pre_inst_state                   false
% 11.66/2.00  --bmc1_pre_inst_reach_state             false
% 11.66/2.00  --bmc1_out_unsat_core                   false
% 11.66/2.00  --bmc1_aig_witness_out                  false
% 11.66/2.00  --bmc1_verbose                          false
% 11.66/2.00  --bmc1_dump_clauses_tptp                false
% 11.66/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.66/2.00  --bmc1_dump_file                        -
% 11.66/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.66/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.66/2.00  --bmc1_ucm_extend_mode                  1
% 11.66/2.00  --bmc1_ucm_init_mode                    2
% 11.66/2.00  --bmc1_ucm_cone_mode                    none
% 11.66/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.66/2.00  --bmc1_ucm_relax_model                  4
% 11.66/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.66/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.66/2.00  --bmc1_ucm_layered_model                none
% 11.66/2.00  --bmc1_ucm_max_lemma_size               10
% 11.66/2.00  
% 11.66/2.00  ------ AIG Options
% 11.66/2.00  
% 11.66/2.00  --aig_mode                              false
% 11.66/2.00  
% 11.66/2.00  ------ Instantiation Options
% 11.66/2.00  
% 11.66/2.00  --instantiation_flag                    true
% 11.66/2.00  --inst_sos_flag                         true
% 11.66/2.00  --inst_sos_phase                        true
% 11.66/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.66/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.66/2.00  --inst_lit_sel_side                     num_symb
% 11.66/2.00  --inst_solver_per_active                1400
% 11.66/2.00  --inst_solver_calls_frac                1.
% 11.66/2.00  --inst_passive_queue_type               priority_queues
% 11.66/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.66/2.00  --inst_passive_queues_freq              [25;2]
% 11.66/2.00  --inst_dismatching                      true
% 11.66/2.00  --inst_eager_unprocessed_to_passive     true
% 11.66/2.00  --inst_prop_sim_given                   true
% 11.66/2.00  --inst_prop_sim_new                     false
% 11.66/2.00  --inst_subs_new                         false
% 11.66/2.00  --inst_eq_res_simp                      false
% 11.66/2.00  --inst_subs_given                       false
% 11.66/2.00  --inst_orphan_elimination               true
% 11.66/2.00  --inst_learning_loop_flag               true
% 11.66/2.00  --inst_learning_start                   3000
% 11.66/2.00  --inst_learning_factor                  2
% 11.66/2.00  --inst_start_prop_sim_after_learn       3
% 11.66/2.00  --inst_sel_renew                        solver
% 11.66/2.00  --inst_lit_activity_flag                true
% 11.66/2.00  --inst_restr_to_given                   false
% 11.66/2.00  --inst_activity_threshold               500
% 11.66/2.00  --inst_out_proof                        true
% 11.66/2.00  
% 11.66/2.00  ------ Resolution Options
% 11.66/2.00  
% 11.66/2.00  --resolution_flag                       true
% 11.66/2.00  --res_lit_sel                           adaptive
% 11.66/2.00  --res_lit_sel_side                      none
% 11.66/2.00  --res_ordering                          kbo
% 11.66/2.00  --res_to_prop_solver                    active
% 11.66/2.00  --res_prop_simpl_new                    false
% 11.66/2.00  --res_prop_simpl_given                  true
% 11.66/2.00  --res_passive_queue_type                priority_queues
% 11.66/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.66/2.00  --res_passive_queues_freq               [15;5]
% 11.66/2.00  --res_forward_subs                      full
% 11.66/2.00  --res_backward_subs                     full
% 11.66/2.00  --res_forward_subs_resolution           true
% 11.66/2.00  --res_backward_subs_resolution          true
% 11.66/2.00  --res_orphan_elimination                true
% 11.66/2.00  --res_time_limit                        2.
% 11.66/2.00  --res_out_proof                         true
% 11.66/2.00  
% 11.66/2.00  ------ Superposition Options
% 11.66/2.00  
% 11.66/2.00  --superposition_flag                    true
% 11.66/2.00  --sup_passive_queue_type                priority_queues
% 11.66/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.66/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.66/2.00  --demod_completeness_check              fast
% 11.66/2.00  --demod_use_ground                      true
% 11.66/2.00  --sup_to_prop_solver                    passive
% 11.66/2.00  --sup_prop_simpl_new                    true
% 11.66/2.00  --sup_prop_simpl_given                  true
% 11.66/2.00  --sup_fun_splitting                     true
% 11.66/2.00  --sup_smt_interval                      50000
% 11.66/2.00  
% 11.66/2.00  ------ Superposition Simplification Setup
% 11.66/2.00  
% 11.66/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.66/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.66/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.66/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.66/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.66/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.66/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.66/2.00  --sup_immed_triv                        [TrivRules]
% 11.66/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_immed_bw_main                     []
% 11.66/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.66/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.66/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_input_bw                          []
% 11.66/2.00  
% 11.66/2.00  ------ Combination Options
% 11.66/2.00  
% 11.66/2.00  --comb_res_mult                         3
% 11.66/2.00  --comb_sup_mult                         2
% 11.66/2.00  --comb_inst_mult                        10
% 11.66/2.00  
% 11.66/2.00  ------ Debug Options
% 11.66/2.00  
% 11.66/2.00  --dbg_backtrace                         false
% 11.66/2.00  --dbg_dump_prop_clauses                 false
% 11.66/2.00  --dbg_dump_prop_clauses_file            -
% 11.66/2.00  --dbg_out_stat                          false
% 11.66/2.00  ------ Parsing...
% 11.66/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.66/2.00  ------ Proving...
% 11.66/2.00  ------ Problem Properties 
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  clauses                                 12
% 11.66/2.00  conjectures                             6
% 11.66/2.00  EPR                                     1
% 11.66/2.00  Horn                                    12
% 11.66/2.00  unary                                   6
% 11.66/2.00  binary                                  0
% 11.66/2.00  lits                                    25
% 11.66/2.00  lits eq                                 8
% 11.66/2.00  fd_pure                                 0
% 11.66/2.00  fd_pseudo                               0
% 11.66/2.00  fd_cond                                 0
% 11.66/2.00  fd_pseudo_cond                          0
% 11.66/2.00  AC symbols                              0
% 11.66/2.00  
% 11.66/2.00  ------ Schedule dynamic 5 is on 
% 11.66/2.00  
% 11.66/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  ------ 
% 11.66/2.00  Current options:
% 11.66/2.00  ------ 
% 11.66/2.00  
% 11.66/2.00  ------ Input Options
% 11.66/2.00  
% 11.66/2.00  --out_options                           all
% 11.66/2.00  --tptp_safe_out                         true
% 11.66/2.00  --problem_path                          ""
% 11.66/2.00  --include_path                          ""
% 11.66/2.00  --clausifier                            res/vclausify_rel
% 11.66/2.00  --clausifier_options                    ""
% 11.66/2.00  --stdin                                 false
% 11.66/2.00  --stats_out                             all
% 11.66/2.00  
% 11.66/2.00  ------ General Options
% 11.66/2.00  
% 11.66/2.00  --fof                                   false
% 11.66/2.00  --time_out_real                         305.
% 11.66/2.00  --time_out_virtual                      -1.
% 11.66/2.00  --symbol_type_check                     false
% 11.66/2.00  --clausify_out                          false
% 11.66/2.00  --sig_cnt_out                           false
% 11.66/2.00  --trig_cnt_out                          false
% 11.66/2.00  --trig_cnt_out_tolerance                1.
% 11.66/2.00  --trig_cnt_out_sk_spl                   false
% 11.66/2.00  --abstr_cl_out                          false
% 11.66/2.00  
% 11.66/2.00  ------ Global Options
% 11.66/2.00  
% 11.66/2.00  --schedule                              default
% 11.66/2.00  --add_important_lit                     false
% 11.66/2.00  --prop_solver_per_cl                    1000
% 11.66/2.00  --min_unsat_core                        false
% 11.66/2.00  --soft_assumptions                      false
% 11.66/2.00  --soft_lemma_size                       3
% 11.66/2.00  --prop_impl_unit_size                   0
% 11.66/2.00  --prop_impl_unit                        []
% 11.66/2.00  --share_sel_clauses                     true
% 11.66/2.00  --reset_solvers                         false
% 11.66/2.00  --bc_imp_inh                            [conj_cone]
% 11.66/2.00  --conj_cone_tolerance                   3.
% 11.66/2.00  --extra_neg_conj                        none
% 11.66/2.00  --large_theory_mode                     true
% 11.66/2.00  --prolific_symb_bound                   200
% 11.66/2.00  --lt_threshold                          2000
% 11.66/2.00  --clause_weak_htbl                      true
% 11.66/2.00  --gc_record_bc_elim                     false
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing Options
% 11.66/2.00  
% 11.66/2.00  --preprocessing_flag                    true
% 11.66/2.00  --time_out_prep_mult                    0.1
% 11.66/2.00  --splitting_mode                        input
% 11.66/2.00  --splitting_grd                         true
% 11.66/2.00  --splitting_cvd                         false
% 11.66/2.00  --splitting_cvd_svl                     false
% 11.66/2.00  --splitting_nvd                         32
% 11.66/2.00  --sub_typing                            true
% 11.66/2.00  --prep_gs_sim                           true
% 11.66/2.00  --prep_unflatten                        true
% 11.66/2.00  --prep_res_sim                          true
% 11.66/2.00  --prep_upred                            true
% 11.66/2.00  --prep_sem_filter                       exhaustive
% 11.66/2.00  --prep_sem_filter_out                   false
% 11.66/2.00  --pred_elim                             true
% 11.66/2.00  --res_sim_input                         true
% 11.66/2.00  --eq_ax_congr_red                       true
% 11.66/2.00  --pure_diseq_elim                       true
% 11.66/2.00  --brand_transform                       false
% 11.66/2.00  --non_eq_to_eq                          false
% 11.66/2.00  --prep_def_merge                        true
% 11.66/2.00  --prep_def_merge_prop_impl              false
% 11.66/2.00  --prep_def_merge_mbd                    true
% 11.66/2.00  --prep_def_merge_tr_red                 false
% 11.66/2.00  --prep_def_merge_tr_cl                  false
% 11.66/2.00  --smt_preprocessing                     true
% 11.66/2.00  --smt_ac_axioms                         fast
% 11.66/2.00  --preprocessed_out                      false
% 11.66/2.00  --preprocessed_stats                    false
% 11.66/2.00  
% 11.66/2.00  ------ Abstraction refinement Options
% 11.66/2.00  
% 11.66/2.00  --abstr_ref                             []
% 11.66/2.00  --abstr_ref_prep                        false
% 11.66/2.00  --abstr_ref_until_sat                   false
% 11.66/2.00  --abstr_ref_sig_restrict                funpre
% 11.66/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.66/2.00  --abstr_ref_under                       []
% 11.66/2.00  
% 11.66/2.00  ------ SAT Options
% 11.66/2.00  
% 11.66/2.00  --sat_mode                              false
% 11.66/2.00  --sat_fm_restart_options                ""
% 11.66/2.00  --sat_gr_def                            false
% 11.66/2.00  --sat_epr_types                         true
% 11.66/2.00  --sat_non_cyclic_types                  false
% 11.66/2.00  --sat_finite_models                     false
% 11.66/2.00  --sat_fm_lemmas                         false
% 11.66/2.00  --sat_fm_prep                           false
% 11.66/2.00  --sat_fm_uc_incr                        true
% 11.66/2.00  --sat_out_model                         small
% 11.66/2.00  --sat_out_clauses                       false
% 11.66/2.00  
% 11.66/2.00  ------ QBF Options
% 11.66/2.00  
% 11.66/2.00  --qbf_mode                              false
% 11.66/2.00  --qbf_elim_univ                         false
% 11.66/2.00  --qbf_dom_inst                          none
% 11.66/2.00  --qbf_dom_pre_inst                      false
% 11.66/2.00  --qbf_sk_in                             false
% 11.66/2.00  --qbf_pred_elim                         true
% 11.66/2.00  --qbf_split                             512
% 11.66/2.00  
% 11.66/2.00  ------ BMC1 Options
% 11.66/2.00  
% 11.66/2.00  --bmc1_incremental                      false
% 11.66/2.00  --bmc1_axioms                           reachable_all
% 11.66/2.00  --bmc1_min_bound                        0
% 11.66/2.00  --bmc1_max_bound                        -1
% 11.66/2.00  --bmc1_max_bound_default                -1
% 11.66/2.00  --bmc1_symbol_reachability              true
% 11.66/2.00  --bmc1_property_lemmas                  false
% 11.66/2.00  --bmc1_k_induction                      false
% 11.66/2.00  --bmc1_non_equiv_states                 false
% 11.66/2.00  --bmc1_deadlock                         false
% 11.66/2.00  --bmc1_ucm                              false
% 11.66/2.00  --bmc1_add_unsat_core                   none
% 11.66/2.00  --bmc1_unsat_core_children              false
% 11.66/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.66/2.00  --bmc1_out_stat                         full
% 11.66/2.00  --bmc1_ground_init                      false
% 11.66/2.00  --bmc1_pre_inst_next_state              false
% 11.66/2.00  --bmc1_pre_inst_state                   false
% 11.66/2.00  --bmc1_pre_inst_reach_state             false
% 11.66/2.00  --bmc1_out_unsat_core                   false
% 11.66/2.00  --bmc1_aig_witness_out                  false
% 11.66/2.00  --bmc1_verbose                          false
% 11.66/2.00  --bmc1_dump_clauses_tptp                false
% 11.66/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.66/2.00  --bmc1_dump_file                        -
% 11.66/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.66/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.66/2.00  --bmc1_ucm_extend_mode                  1
% 11.66/2.00  --bmc1_ucm_init_mode                    2
% 11.66/2.00  --bmc1_ucm_cone_mode                    none
% 11.66/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.66/2.00  --bmc1_ucm_relax_model                  4
% 11.66/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.66/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.66/2.00  --bmc1_ucm_layered_model                none
% 11.66/2.00  --bmc1_ucm_max_lemma_size               10
% 11.66/2.00  
% 11.66/2.00  ------ AIG Options
% 11.66/2.00  
% 11.66/2.00  --aig_mode                              false
% 11.66/2.00  
% 11.66/2.00  ------ Instantiation Options
% 11.66/2.00  
% 11.66/2.00  --instantiation_flag                    true
% 11.66/2.00  --inst_sos_flag                         true
% 11.66/2.00  --inst_sos_phase                        true
% 11.66/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.66/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.66/2.00  --inst_lit_sel_side                     none
% 11.66/2.00  --inst_solver_per_active                1400
% 11.66/2.00  --inst_solver_calls_frac                1.
% 11.66/2.00  --inst_passive_queue_type               priority_queues
% 11.66/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.66/2.00  --inst_passive_queues_freq              [25;2]
% 11.66/2.00  --inst_dismatching                      true
% 11.66/2.00  --inst_eager_unprocessed_to_passive     true
% 11.66/2.00  --inst_prop_sim_given                   true
% 11.66/2.00  --inst_prop_sim_new                     false
% 11.66/2.00  --inst_subs_new                         false
% 11.66/2.00  --inst_eq_res_simp                      false
% 11.66/2.00  --inst_subs_given                       false
% 11.66/2.00  --inst_orphan_elimination               true
% 11.66/2.00  --inst_learning_loop_flag               true
% 11.66/2.00  --inst_learning_start                   3000
% 11.66/2.00  --inst_learning_factor                  2
% 11.66/2.00  --inst_start_prop_sim_after_learn       3
% 11.66/2.00  --inst_sel_renew                        solver
% 11.66/2.00  --inst_lit_activity_flag                true
% 11.66/2.00  --inst_restr_to_given                   false
% 11.66/2.00  --inst_activity_threshold               500
% 11.66/2.00  --inst_out_proof                        true
% 11.66/2.00  
% 11.66/2.00  ------ Resolution Options
% 11.66/2.00  
% 11.66/2.00  --resolution_flag                       false
% 11.66/2.00  --res_lit_sel                           adaptive
% 11.66/2.00  --res_lit_sel_side                      none
% 11.66/2.00  --res_ordering                          kbo
% 11.66/2.00  --res_to_prop_solver                    active
% 11.66/2.00  --res_prop_simpl_new                    false
% 11.66/2.00  --res_prop_simpl_given                  true
% 11.66/2.00  --res_passive_queue_type                priority_queues
% 11.66/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.66/2.00  --res_passive_queues_freq               [15;5]
% 11.66/2.00  --res_forward_subs                      full
% 11.66/2.00  --res_backward_subs                     full
% 11.66/2.00  --res_forward_subs_resolution           true
% 11.66/2.00  --res_backward_subs_resolution          true
% 11.66/2.00  --res_orphan_elimination                true
% 11.66/2.00  --res_time_limit                        2.
% 11.66/2.00  --res_out_proof                         true
% 11.66/2.00  
% 11.66/2.00  ------ Superposition Options
% 11.66/2.00  
% 11.66/2.00  --superposition_flag                    true
% 11.66/2.00  --sup_passive_queue_type                priority_queues
% 11.66/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.66/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.66/2.00  --demod_completeness_check              fast
% 11.66/2.00  --demod_use_ground                      true
% 11.66/2.00  --sup_to_prop_solver                    passive
% 11.66/2.00  --sup_prop_simpl_new                    true
% 11.66/2.00  --sup_prop_simpl_given                  true
% 11.66/2.00  --sup_fun_splitting                     true
% 11.66/2.00  --sup_smt_interval                      50000
% 11.66/2.00  
% 11.66/2.00  ------ Superposition Simplification Setup
% 11.66/2.00  
% 11.66/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.66/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.66/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.66/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.66/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.66/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.66/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.66/2.00  --sup_immed_triv                        [TrivRules]
% 11.66/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_immed_bw_main                     []
% 11.66/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.66/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.66/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_input_bw                          []
% 11.66/2.00  
% 11.66/2.00  ------ Combination Options
% 11.66/2.00  
% 11.66/2.00  --comb_res_mult                         3
% 11.66/2.00  --comb_sup_mult                         2
% 11.66/2.00  --comb_inst_mult                        10
% 11.66/2.00  
% 11.66/2.00  ------ Debug Options
% 11.66/2.00  
% 11.66/2.00  --dbg_backtrace                         false
% 11.66/2.00  --dbg_dump_prop_clauses                 false
% 11.66/2.00  --dbg_dump_prop_clauses_file            -
% 11.66/2.00  --dbg_out_stat                          false
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  ------ Proving...
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  % SZS status Theorem for theBenchmark.p
% 11.66/2.00  
% 11.66/2.00   Resolution empty clause
% 11.66/2.00  
% 11.66/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.66/2.00  
% 11.66/2.00  fof(f10,conjecture,(
% 11.66/2.00    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f11,negated_conjecture,(
% 11.66/2.00    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 11.66/2.00    inference(negated_conjecture,[],[f10])).
% 11.66/2.00  
% 11.66/2.00  fof(f32,plain,(
% 11.66/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f11])).
% 11.66/2.00  
% 11.66/2.00  fof(f33,plain,(
% 11.66/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f32])).
% 11.66/2.00  
% 11.66/2.00  fof(f38,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK3 != X2 & k3_lattices(X0,X1,sK3) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK3) = k4_lattices(X0,X1,X2) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 11.66/2.00    introduced(choice_axiom,[])).
% 11.66/2.00  
% 11.66/2.00  fof(f37,plain,(
% 11.66/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK2 != X3 & k3_lattices(X0,X1,sK2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 11.66/2.00    introduced(choice_axiom,[])).
% 11.66/2.00  
% 11.66/2.00  fof(f36,plain,(
% 11.66/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK1,X2) = k3_lattices(X0,sK1,X3) & k4_lattices(X0,sK1,X2) = k4_lattices(X0,sK1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 11.66/2.00    introduced(choice_axiom,[])).
% 11.66/2.00  
% 11.66/2.00  fof(f35,plain,(
% 11.66/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 11.66/2.00    introduced(choice_axiom,[])).
% 11.66/2.00  
% 11.66/2.00  fof(f39,plain,(
% 11.66/2.00    (((sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 11.66/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f38,f37,f36,f35])).
% 11.66/2.00  
% 11.66/2.00  fof(f58,plain,(
% 11.66/2.00    m1_subset_1(sK1,u1_struct_0(sK0))),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f60,plain,(
% 11.66/2.00    m1_subset_1(sK3,u1_struct_0(sK0))),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f5,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f23,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f5])).
% 11.66/2.00  
% 11.66/2.00  fof(f24,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f23])).
% 11.66/2.00  
% 11.66/2.00  fof(f48,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f24])).
% 11.66/2.00  
% 11.66/2.00  fof(f1,axiom,(
% 11.66/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f12,plain,(
% 11.66/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.66/2.00    inference(pure_predicate_removal,[],[f1])).
% 11.66/2.00  
% 11.66/2.00  fof(f13,plain,(
% 11.66/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.66/2.00    inference(pure_predicate_removal,[],[f12])).
% 11.66/2.00  
% 11.66/2.00  fof(f14,plain,(
% 11.66/2.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.66/2.00    inference(pure_predicate_removal,[],[f13])).
% 11.66/2.00  
% 11.66/2.00  fof(f15,plain,(
% 11.66/2.00    ! [X0] : (((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 11.66/2.00    inference(ennf_transformation,[],[f14])).
% 11.66/2.00  
% 11.66/2.00  fof(f16,plain,(
% 11.66/2.00    ! [X0] : ((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 11.66/2.00    inference(flattening,[],[f15])).
% 11.66/2.00  
% 11.66/2.00  fof(f42,plain,(
% 11.66/2.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f16])).
% 11.66/2.00  
% 11.66/2.00  fof(f55,plain,(
% 11.66/2.00    v10_lattices(sK0)),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f54,plain,(
% 11.66/2.00    ~v2_struct_0(sK0)),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f57,plain,(
% 11.66/2.00    l3_lattices(sK0)),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f6,axiom,(
% 11.66/2.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f25,plain,(
% 11.66/2.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 11.66/2.00    inference(ennf_transformation,[],[f6])).
% 11.66/2.00  
% 11.66/2.00  fof(f49,plain,(
% 11.66/2.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f25])).
% 11.66/2.00  
% 11.66/2.00  fof(f7,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f26,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f7])).
% 11.66/2.00  
% 11.66/2.00  fof(f27,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f26])).
% 11.66/2.00  
% 11.66/2.00  fof(f51,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f27])).
% 11.66/2.00  
% 11.66/2.00  fof(f41,plain,(
% 11.66/2.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f16])).
% 11.66/2.00  
% 11.66/2.00  fof(f50,plain,(
% 11.66/2.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f25])).
% 11.66/2.00  
% 11.66/2.00  fof(f59,plain,(
% 11.66/2.00    m1_subset_1(sK2,u1_struct_0(sK0))),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f3,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f19,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f3])).
% 11.66/2.00  
% 11.66/2.00  fof(f20,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f19])).
% 11.66/2.00  
% 11.66/2.00  fof(f45,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f20])).
% 11.66/2.00  
% 11.66/2.00  fof(f61,plain,(
% 11.66/2.00    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f43,plain,(
% 11.66/2.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f16])).
% 11.66/2.00  
% 11.66/2.00  fof(f8,axiom,(
% 11.66/2.00    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f28,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f8])).
% 11.66/2.00  
% 11.66/2.00  fof(f29,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f28])).
% 11.66/2.00  
% 11.66/2.00  fof(f52,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f29])).
% 11.66/2.00  
% 11.66/2.00  fof(f4,axiom,(
% 11.66/2.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f21,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f4])).
% 11.66/2.00  
% 11.66/2.00  fof(f22,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f21])).
% 11.66/2.00  
% 11.66/2.00  fof(f34,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(nnf_transformation,[],[f22])).
% 11.66/2.00  
% 11.66/2.00  fof(f46,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f34])).
% 11.66/2.00  
% 11.66/2.00  fof(f9,axiom,(
% 11.66/2.00    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f30,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f9])).
% 11.66/2.00  
% 11.66/2.00  fof(f31,plain,(
% 11.66/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f30])).
% 11.66/2.00  
% 11.66/2.00  fof(f53,plain,(
% 11.66/2.00    ( ! [X2,X0,X3,X1] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f31])).
% 11.66/2.00  
% 11.66/2.00  fof(f56,plain,(
% 11.66/2.00    v11_lattices(sK0)),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f2,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f17,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 11.66/2.00    inference(ennf_transformation,[],[f2])).
% 11.66/2.00  
% 11.66/2.00  fof(f18,plain,(
% 11.66/2.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 11.66/2.00    inference(flattening,[],[f17])).
% 11.66/2.00  
% 11.66/2.00  fof(f44,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f18])).
% 11.66/2.00  
% 11.66/2.00  fof(f62,plain,(
% 11.66/2.00    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  fof(f63,plain,(
% 11.66/2.00    sK2 != sK3),
% 11.66/2.00    inference(cnf_transformation,[],[f39])).
% 11.66/2.00  
% 11.66/2.00  cnf(c_19,negated_conjecture,
% 11.66/2.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_612,negated_conjecture,
% 11.66/2.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_19]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_783,plain,
% 11.66/2.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_17,negated_conjecture,
% 11.66/2.00      ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_614,negated_conjecture,
% 11.66/2.00      ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_17]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_781,plain,
% 11.66/2.00      ( m1_subset_1(sK3,u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 11.66/2.00      | ~ l1_lattices(X1)
% 11.66/2.00      | ~ v6_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1) ),
% 11.66/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1,plain,
% 11.66/2.00      ( v6_lattices(X0)
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v10_lattices(X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_22,negated_conjecture,
% 11.66/2.00      ( v10_lattices(sK0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_324,plain,
% 11.66/2.00      ( v6_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK0 != X0 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_325,plain,
% 11.66/2.00      ( v6_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_324]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_23,negated_conjecture,
% 11.66/2.00      ( ~ v2_struct_0(sK0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_20,negated_conjecture,
% 11.66/2.00      ( l3_lattices(sK0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_66,plain,
% 11.66/2.00      ( v6_lattices(sK0)
% 11.66/2.00      | ~ l3_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0)
% 11.66/2.00      | ~ v10_lattices(sK0) ),
% 11.66/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_327,plain,
% 11.66/2.00      ( v6_lattices(sK0) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_325,c_23,c_22,c_20,c_66]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_361,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 11.66/2.00      | ~ l1_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | sK0 != X1 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_8,c_327]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_362,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
% 11.66/2.00      | ~ l1_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_361]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_10,plain,
% 11.66/2.00      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_41,plain,
% 11.66/2.00      ( l1_lattices(sK0) | ~ l3_lattices(sK0) ),
% 11.66/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_366,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_362,c_23,c_20,c_41]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_610,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 11.66/2.00      | m1_subset_1(k4_lattices(sK0,X0_47,X1_47),u1_struct_0(sK0)) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_366]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_785,plain,
% 11.66/2.00      ( m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(k4_lattices(sK0,X0_47,X1_47),u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_11,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ l2_lattices(X1)
% 11.66/2.00      | ~ v4_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2,plain,
% 11.66/2.00      ( v4_lattices(X0)
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v10_lattices(X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_313,plain,
% 11.66/2.00      ( v4_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK0 != X0 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_2,c_22]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_314,plain,
% 11.66/2.00      ( v4_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_313]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_63,plain,
% 11.66/2.00      ( v4_lattices(sK0)
% 11.66/2.00      | ~ l3_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0)
% 11.66/2.00      | ~ v10_lattices(sK0) ),
% 11.66/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_316,plain,
% 11.66/2.00      ( v4_lattices(sK0) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_314,c_23,c_22,c_20,c_63]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_411,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ l2_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 11.66/2.00      | sK0 != X1 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_316]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_412,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ l2_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0)
% 11.66/2.00      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_411]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_9,plain,
% 11.66/2.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_44,plain,
% 11.66/2.00      ( l2_lattices(sK0) | ~ l3_lattices(sK0) ),
% 11.66/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_416,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_412,c_23,c_20,c_44]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_608,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 11.66/2.00      | k1_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X0_47,X1_47) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_416]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_787,plain,
% 11.66/2.00      ( k1_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X0_47,X1_47)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2189,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),X2_47) = k3_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),X2_47)
% 11.66/2.00      | m1_subset_1(X2_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_785,c_787]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_27192,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK3) = k3_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK3)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_2189]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_28278,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK3)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_27192]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_28552,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK3) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_28278]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_18,negated_conjecture,
% 11.66/2.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_613,negated_conjecture,
% 11.66/2.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_18]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_782,plain,
% 11.66/2.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_5,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ l1_lattices(X1)
% 11.66/2.00      | ~ v6_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_382,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ l1_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 11.66/2.00      | sK0 != X1 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_5,c_327]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_383,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ l1_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0)
% 11.66/2.00      | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_382]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_387,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_383,c_23,c_20,c_41]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_609,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 11.66/2.00      | k4_lattices(sK0,X0_47,X1_47) = k4_lattices(sK0,X1_47,X0_47) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_387]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_786,plain,
% 11.66/2.00      ( k4_lattices(sK0,X0_47,X1_47) = k4_lattices(sK0,X1_47,X0_47)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1501,plain,
% 11.66/2.00      ( k4_lattices(sK0,X0_47,sK2) = k4_lattices(sK0,sK2,X0_47)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_786]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1867,plain,
% 11.66/2.00      ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK1,sK2) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_1501]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1500,plain,
% 11.66/2.00      ( k4_lattices(sK0,X0_47,sK3) = k4_lattices(sK0,sK3,X0_47)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_786]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1521,plain,
% 11.66/2.00      ( k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_1500]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_16,negated_conjecture,
% 11.66/2.00      ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_615,negated_conjecture,
% 11.66/2.00      ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_16]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1647,plain,
% 11.66/2.00      ( k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK2) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_1521,c_615]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1873,plain,
% 11.66/2.00      ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK3,sK1) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_1867,c_1647]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_0,plain,
% 11.66/2.00      ( ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v10_lattices(X0)
% 11.66/2.00      | v8_lattices(X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_12,plain,
% 11.66/2.00      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ v6_lattices(X0)
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v8_lattices(X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_256,plain,
% 11.66/2.00      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ v6_lattices(X0)
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v10_lattices(X0) ),
% 11.66/2.00      inference(resolution,[status(thm)],[c_0,c_12]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_260,plain,
% 11.66/2.00      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v10_lattices(X0) ),
% 11.66/2.00      inference(global_propositional_subsumption,[status(thm)],[c_256,c_1]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_261,plain,
% 11.66/2.00      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | ~ v10_lattices(X0) ),
% 11.66/2.00      inference(renaming,[status(thm)],[c_260]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_292,plain,
% 11.66/2.00      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ l3_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | sK0 != X0 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_261,c_22]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_293,plain,
% 11.66/2.00      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ l3_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_292]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_297,plain,
% 11.66/2.00      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_293,c_23,c_20]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_298,plain,
% 11.66/2.00      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
% 11.66/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 11.66/2.00      inference(renaming,[status(thm)],[c_297]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7,plain,
% 11.66/2.00      ( ~ r1_lattices(X0,X1,X2)
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ l2_lattices(X0)
% 11.66/2.00      | v2_struct_0(X0)
% 11.66/2.00      | k1_lattices(X0,X1,X2) = X2 ),
% 11.66/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_461,plain,
% 11.66/2.00      ( ~ r1_lattices(X0,X1,X2)
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/2.00      | ~ l2_lattices(X0)
% 11.66/2.00      | k1_lattices(X0,X1,X2) = X2
% 11.66/2.00      | sK0 != X0 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_462,plain,
% 11.66/2.00      ( ~ r1_lattices(sK0,X0,X1)
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ l2_lattices(sK0)
% 11.66/2.00      | k1_lattices(sK0,X0,X1) = X1 ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_461]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_466,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ r1_lattices(sK0,X0,X1)
% 11.66/2.00      | k1_lattices(sK0,X0,X1) = X1 ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_462,c_20,c_44]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_467,plain,
% 11.66/2.00      ( ~ r1_lattices(sK0,X0,X1)
% 11.66/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | k1_lattices(sK0,X0,X1) = X1 ),
% 11.66/2.00      inference(renaming,[status(thm)],[c_466]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_520,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X3,u1_struct_0(sK0))
% 11.66/2.00      | X0 != X2
% 11.66/2.00      | k1_lattices(sK0,X1,X0) = X0
% 11.66/2.00      | k4_lattices(sK0,X2,X3) != X1
% 11.66/2.00      | sK0 != sK0 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_298,c_467]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_521,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(k4_lattices(sK0,X1,X0),u1_struct_0(sK0))
% 11.66/2.00      | k1_lattices(sK0,k4_lattices(sK0,X1,X0),X1) = X1 ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_520]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_533,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | k1_lattices(sK0,k4_lattices(sK0,X1,X0),X1) = X1 ),
% 11.66/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_521,c_366]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_606,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 11.66/2.00      | k1_lattices(sK0,k4_lattices(sK0,X1_47,X0_47),X1_47) = X1_47 ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_533]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_789,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),X0_47) = X0_47
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3722,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK3) = sK3
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_789]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3739,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK3) = sK3 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_3722]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3741,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK3) = sK3 ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_3739,c_1873]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_13,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.66/2.00      | ~ v11_lattices(X1)
% 11.66/2.00      | ~ l3_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | ~ v10_lattices(X1)
% 11.66/2.00      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_21,negated_conjecture,
% 11.66/2.00      ( v11_lattices(sK0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_227,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.66/2.00      | ~ l3_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | ~ v10_lattices(X1)
% 11.66/2.00      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
% 11.66/2.00      | sK0 != X1 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_228,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 11.66/2.00      | ~ l3_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0)
% 11.66/2.00      | ~ v10_lattices(sK0)
% 11.66/2.00      | k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X0)) = k3_lattices(sK0,X1,k4_lattices(sK0,X2,X0)) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_227]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_232,plain,
% 11.66/2.00      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X0)) = k3_lattices(sK0,X1,k4_lattices(sK0,X2,X0)) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_228,c_23,c_22,c_20]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_233,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 11.66/2.00      | k4_lattices(sK0,k3_lattices(sK0,X2,X0),k3_lattices(sK0,X2,X1)) = k3_lattices(sK0,X2,k4_lattices(sK0,X0,X1)) ),
% 11.66/2.00      inference(renaming,[status(thm)],[c_232]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_611,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X2_47,u1_struct_0(sK0))
% 11.66/2.00      | k4_lattices(sK0,k3_lattices(sK0,X2_47,X0_47),k3_lattices(sK0,X2_47,X1_47)) = k3_lattices(sK0,X2_47,k4_lattices(sK0,X0_47,X1_47)) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_233]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_784,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,X0_47,X1_47),k3_lattices(sK0,X0_47,X2_47)) = k3_lattices(sK0,X0_47,k4_lattices(sK0,X1_47,X2_47))
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X2_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_936,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,X0_47,X1_47),k3_lattices(sK0,X0_47,sK2)) = k3_lattices(sK0,X0_47,k4_lattices(sK0,X1_47,sK2))
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_784]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4553,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,sK3,X0_47),k3_lattices(sK0,sK3,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,X0_47,sK2))
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_936]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ l2_lattices(X1)
% 11.66/2.00      | ~ v4_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_432,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.66/2.00      | ~ l2_lattices(X1)
% 11.66/2.00      | v2_struct_0(X1)
% 11.66/2.00      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 11.66/2.00      | sK0 != X1 ),
% 11.66/2.00      inference(resolution_lifted,[status(thm)],[c_4,c_316]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_433,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | ~ l2_lattices(sK0)
% 11.66/2.00      | v2_struct_0(sK0)
% 11.66/2.00      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 11.66/2.00      inference(unflattening,[status(thm)],[c_432]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_437,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 11.66/2.00      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_433,c_23,c_20,c_44]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_607,plain,
% 11.66/2.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 11.66/2.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 11.66/2.00      | k3_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X1_47,X0_47) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_437]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_788,plain,
% 11.66/2.00      ( k3_lattices(sK0,X0_47,X1_47) = k3_lattices(sK0,X1_47,X0_47)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2952,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK3,X0_47) = k3_lattices(sK0,X0_47,sK3)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_788]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3071,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK3,sK2) = k3_lattices(sK0,sK2,sK3) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_2952]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4558,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,sK3,X0_47),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,X0_47,sK2))
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_4553,c_3071]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_21692,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_4558]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2953,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,X0_47) = k3_lattices(sK0,X0_47,sK2)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_788]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3356,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_2953]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3072,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_2952]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_15,negated_conjecture,
% 11.66/2.00      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_616,negated_conjecture,
% 11.66/2.00      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_15]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3159,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK2) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_3072,c_616]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3361,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK3,sK1) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_3356,c_3159]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_935,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,X0_47,X1_47),k3_lattices(sK0,X0_47,sK3)) = k3_lattices(sK0,X0_47,k4_lattices(sK0,X1_47,sK3))
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_784]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_947,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,sK2,X0_47),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,X0_47,sK3))
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_935]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4797,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_947]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1957,plain,
% 11.66/2.00      ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK1,sK3) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_1873,c_1521]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4799,plain,
% 11.66/2.00      ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_4797,c_1957]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_21703,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) ),
% 11.66/2.00      inference(light_normalisation,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_21692,c_1867,c_3361,c_4799]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1010,plain,
% 11.66/2.00      ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) = iProver_top
% 11.66/2.00      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(sK3,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_615,c_785]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_28,plain,
% 11.66/2.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_30,plain,
% 11.66/2.00      ( m1_subset_1(sK3,u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1021,plain,
% 11.66/2.00      ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(global_propositional_subsumption,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_1010,c_28,c_30]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1746,plain,
% 11.66/2.00      ( m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_1647,c_1021]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1956,plain,
% 11.66/2.00      ( m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) = iProver_top ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_1873,c_1746]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_11241,plain,
% 11.66/2.00      ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_1956,c_2952]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_22085,plain,
% 11.66/2.00      ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK3) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_21703,c_11241]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_28562,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = sK3 ),
% 11.66/2.00      inference(light_normalisation,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_28552,c_1873,c_3741,c_22085]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_27193,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK2) = k3_lattices(sK0,k4_lattices(sK0,X0_47,X1_47),sK2)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 11.66/2.00      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_2189]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_29498,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK3,X0_47),sK2)
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_781,c_27193]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_30169,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK2) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_29498]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3723,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK2,X0_47),sK2) = sK2
% 11.66/2.00      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_782,c_789]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3855,plain,
% 11.66/2.00      ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK2) = sK2 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_783,c_3723]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_11240,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK2) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_1956,c_2953]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_30178,plain,
% 11.66/2.00      ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = sK2 ),
% 11.66/2.00      inference(light_normalisation,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_30169,c_1873,c_3855,c_11240]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_33067,plain,
% 11.66/2.00      ( sK3 = sK2 ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_28562,c_30178]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_14,negated_conjecture,
% 11.66/2.00      ( sK2 != sK3 ),
% 11.66/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_617,negated_conjecture,
% 11.66/2.00      ( sK2 != sK3 ),
% 11.66/2.00      inference(subtyping,[status(esa)],[c_14]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_33217,plain,
% 11.66/2.00      ( sK2 != sK2 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_33067,c_617]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_33218,plain,
% 11.66/2.00      ( $false ),
% 11.66/2.00      inference(equality_resolution_simp,[status(thm)],[c_33217]) ).
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.66/2.00  
% 11.66/2.00  ------                               Statistics
% 11.66/2.00  
% 11.66/2.00  ------ General
% 11.66/2.00  
% 11.66/2.00  abstr_ref_over_cycles:                  0
% 11.66/2.00  abstr_ref_under_cycles:                 0
% 11.66/2.00  gc_basic_clause_elim:                   0
% 11.66/2.00  forced_gc_time:                         0
% 11.66/2.00  parsing_time:                           0.009
% 11.66/2.00  unif_index_cands_time:                  0.
% 11.66/2.00  unif_index_add_time:                    0.
% 11.66/2.00  orderings_time:                         0.
% 11.66/2.00  out_proof_time:                         0.01
% 11.66/2.00  total_time:                             1.02
% 11.66/2.00  num_of_symbols:                         50
% 11.66/2.00  num_of_terms:                           23212
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing
% 11.66/2.00  
% 11.66/2.00  num_of_splits:                          0
% 11.66/2.00  num_of_split_atoms:                     0
% 11.66/2.00  num_of_reused_defs:                     0
% 11.66/2.00  num_eq_ax_congr_red:                    17
% 11.66/2.00  num_of_sem_filtered_clauses:            1
% 11.66/2.00  num_of_subtypes:                        3
% 11.66/2.00  monotx_restored_types:                  0
% 11.66/2.00  sat_num_of_epr_types:                   0
% 11.66/2.00  sat_num_of_non_cyclic_types:            0
% 11.66/2.00  sat_guarded_non_collapsed_types:        1
% 11.66/2.00  num_pure_diseq_elim:                    0
% 11.66/2.00  simp_replaced_by:                       0
% 11.66/2.00  res_preprocessed:                       72
% 11.66/2.00  prep_upred:                             0
% 11.66/2.00  prep_unflattend:                        14
% 11.66/2.00  smt_new_axioms:                         0
% 11.66/2.00  pred_elim_cands:                        1
% 11.66/2.00  pred_elim:                              10
% 11.66/2.00  pred_elim_cl:                           11
% 11.66/2.00  pred_elim_cycles:                       12
% 11.66/2.00  merged_defs:                            0
% 11.66/2.00  merged_defs_ncl:                        0
% 11.66/2.00  bin_hyper_res:                          0
% 11.66/2.00  prep_cycles:                            4
% 11.66/2.00  pred_elim_time:                         0.006
% 11.66/2.00  splitting_time:                         0.
% 11.66/2.00  sem_filter_time:                        0.
% 11.66/2.00  monotx_time:                            0.
% 11.66/2.00  subtype_inf_time:                       0.
% 11.66/2.00  
% 11.66/2.00  ------ Problem properties
% 11.66/2.00  
% 11.66/2.00  clauses:                                12
% 11.66/2.00  conjectures:                            6
% 11.66/2.00  epr:                                    1
% 11.66/2.00  horn:                                   12
% 11.66/2.00  ground:                                 6
% 11.66/2.00  unary:                                  6
% 11.66/2.00  binary:                                 0
% 11.66/2.00  lits:                                   25
% 11.66/2.00  lits_eq:                                8
% 11.66/2.00  fd_pure:                                0
% 11.66/2.00  fd_pseudo:                              0
% 11.66/2.00  fd_cond:                                0
% 11.66/2.00  fd_pseudo_cond:                         0
% 11.66/2.00  ac_symbols:                             0
% 11.66/2.00  
% 11.66/2.00  ------ Propositional Solver
% 11.66/2.00  
% 11.66/2.00  prop_solver_calls:                      36
% 11.66/2.00  prop_fast_solver_calls:                 1028
% 11.66/2.00  smt_solver_calls:                       0
% 11.66/2.00  smt_fast_solver_calls:                  0
% 11.66/2.00  prop_num_of_clauses:                    10789
% 11.66/2.00  prop_preprocess_simplified:             20419
% 11.66/2.00  prop_fo_subsumed:                       22
% 11.66/2.00  prop_solver_time:                       0.
% 11.66/2.00  smt_solver_time:                        0.
% 11.66/2.00  smt_fast_solver_time:                   0.
% 11.66/2.00  prop_fast_solver_time:                  0.
% 11.66/2.00  prop_unsat_core_time:                   0.
% 11.66/2.00  
% 11.66/2.00  ------ QBF
% 11.66/2.00  
% 11.66/2.00  qbf_q_res:                              0
% 11.66/2.00  qbf_num_tautologies:                    0
% 11.66/2.00  qbf_prep_cycles:                        0
% 11.66/2.00  
% 11.66/2.00  ------ BMC1
% 11.66/2.00  
% 11.66/2.00  bmc1_current_bound:                     -1
% 11.66/2.00  bmc1_last_solved_bound:                 -1
% 11.66/2.00  bmc1_unsat_core_size:                   -1
% 11.66/2.00  bmc1_unsat_core_parents_size:           -1
% 11.66/2.00  bmc1_merge_next_fun:                    0
% 11.66/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.66/2.00  
% 11.66/2.00  ------ Instantiation
% 11.66/2.00  
% 11.66/2.00  inst_num_of_clauses:                    4360
% 11.66/2.00  inst_num_in_passive:                    2392
% 11.66/2.00  inst_num_in_active:                     1583
% 11.66/2.00  inst_num_in_unprocessed:                385
% 11.66/2.00  inst_num_of_loops:                      1640
% 11.66/2.00  inst_num_of_learning_restarts:          0
% 11.66/2.00  inst_num_moves_active_passive:          49
% 11.66/2.00  inst_lit_activity:                      0
% 11.66/2.00  inst_lit_activity_moves:                0
% 11.66/2.00  inst_num_tautologies:                   0
% 11.66/2.00  inst_num_prop_implied:                  0
% 11.66/2.00  inst_num_existing_simplified:           0
% 11.66/2.00  inst_num_eq_res_simplified:             0
% 11.66/2.00  inst_num_child_elim:                    0
% 11.66/2.00  inst_num_of_dismatching_blockings:      6480
% 11.66/2.00  inst_num_of_non_proper_insts:           7780
% 11.66/2.00  inst_num_of_duplicates:                 0
% 11.66/2.00  inst_inst_num_from_inst_to_res:         0
% 11.66/2.00  inst_dismatching_checking_time:         0.
% 11.66/2.00  
% 11.66/2.00  ------ Resolution
% 11.66/2.00  
% 11.66/2.00  res_num_of_clauses:                     0
% 11.66/2.00  res_num_in_passive:                     0
% 11.66/2.00  res_num_in_active:                      0
% 11.66/2.00  res_num_of_loops:                       76
% 11.66/2.00  res_forward_subset_subsumed:            351
% 11.66/2.00  res_backward_subset_subsumed:           0
% 11.66/2.00  res_forward_subsumed:                   0
% 11.66/2.00  res_backward_subsumed:                  0
% 11.66/2.00  res_forward_subsumption_resolution:     1
% 11.66/2.00  res_backward_subsumption_resolution:    0
% 11.66/2.00  res_clause_to_clause_subsumption:       4375
% 11.66/2.00  res_orphan_elimination:                 0
% 11.66/2.00  res_tautology_del:                      750
% 11.66/2.00  res_num_eq_res_simplified:              0
% 11.66/2.00  res_num_sel_changes:                    0
% 11.66/2.00  res_moves_from_active_to_pass:          0
% 11.66/2.00  
% 11.66/2.00  ------ Superposition
% 11.66/2.00  
% 11.66/2.00  sup_time_total:                         0.
% 11.66/2.00  sup_time_generating:                    0.
% 11.66/2.00  sup_time_sim_full:                      0.
% 11.66/2.00  sup_time_sim_immed:                     0.
% 11.66/2.00  
% 11.66/2.00  sup_num_of_clauses:                     1115
% 11.66/2.00  sup_num_in_active:                      121
% 11.66/2.00  sup_num_in_passive:                     994
% 11.66/2.00  sup_num_of_loops:                       327
% 11.66/2.00  sup_fw_superposition:                   802
% 11.66/2.00  sup_bw_superposition:                   627
% 11.66/2.00  sup_immediate_simplified:               173
% 11.66/2.00  sup_given_eliminated:                   3
% 11.66/2.00  comparisons_done:                       0
% 11.66/2.00  comparisons_avoided:                    0
% 11.66/2.00  
% 11.66/2.00  ------ Simplifications
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  sim_fw_subset_subsumed:                 2
% 11.66/2.00  sim_bw_subset_subsumed:                 0
% 11.66/2.00  sim_fw_subsumed:                        29
% 11.66/2.00  sim_bw_subsumed:                        0
% 11.66/2.00  sim_fw_subsumption_res:                 0
% 11.66/2.00  sim_bw_subsumption_res:                 0
% 11.66/2.00  sim_tautology_del:                      0
% 11.66/2.00  sim_eq_tautology_del:                   49
% 11.66/2.00  sim_eq_res_simp:                        0
% 11.66/2.00  sim_fw_demodulated:                     7
% 11.66/2.00  sim_bw_demodulated:                     209
% 11.66/2.00  sim_light_normalised:                   166
% 11.66/2.00  sim_joinable_taut:                      0
% 11.66/2.00  sim_joinable_simp:                      0
% 11.66/2.00  sim_ac_normalised:                      0
% 11.66/2.00  sim_smt_subsumption:                    0
% 11.66/2.00  
%------------------------------------------------------------------------------

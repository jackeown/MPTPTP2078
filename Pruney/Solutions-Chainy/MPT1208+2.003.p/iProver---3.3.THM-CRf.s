%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:19 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  233 (1182 expanded)
%              Number of clauses        :  151 ( 322 expanded)
%              Number of leaves         :   23 ( 300 expanded)
%              Depth                    :   18
%              Number of atoms          : 1165 (6634 expanded)
%              Number of equality atoms :  195 ( 899 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k4_lattices(X0,k6_lattices(X0),sK7) != sK7
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,k6_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK6,k6_lattices(sK6),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l3_lattices(sK6)
      & v14_lattices(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l3_lattices(sK6)
    & v14_lattices(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f45,f64,f63])).

fof(f103,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK0(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK0(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f101,plain,(
    v14_lattices(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f99,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f69,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f68,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK5(X0)),sK5(X0)) != sK5(X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) != sK5(X0)
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f57,f59,f58])).

fof(f82,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f67,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1433,plain,
    ( ~ r1_lattices(X0_58,X0_56,X1_56)
    | r1_lattices(X0_58,X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_3217,plain,
    ( ~ r1_lattices(sK6,X0_56,X1_56)
    | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != X1_56
    | sK7 != X0_56 ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_3354,plain,
    ( ~ r1_lattices(sK6,X0_56,k2_lattices(sK6,k6_lattices(sK6),sK7))
    | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
    | sK7 != X0_56 ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_6179,plain,
    ( ~ r1_lattices(sK6,k2_lattices(sK6,X0_56,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
    | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
    | sK7 != k2_lattices(sK6,X0_56,sK7) ),
    inference(instantiation,[status(thm)],[c_3354])).

cnf(c_6187,plain,
    ( ~ r1_lattices(sK6,k2_lattices(sK6,sK7,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
    | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
    | sK7 != k2_lattices(sK6,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_6179])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1422,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1750,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1422])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v14_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_36,negated_conjecture,
    ( v14_lattices(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_36])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ l2_lattices(sK6)
    | v2_struct_0(sK6)
    | k1_lattices(sK6,X0,k6_lattices(sK6)) = k6_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_35,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_22,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_75,plain,
    ( l2_lattices(sK6)
    | ~ l3_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_78,plain,
    ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ l2_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k1_lattices(sK6,X0,k6_lattices(sK6)) = k6_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_38,c_35,c_75,c_78])).

cnf(c_1420,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | k1_lattices(sK6,X0_56,k6_lattices(sK6)) = k6_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_587])).

cnf(c_1752,plain,
    ( k1_lattices(sK6,X0_56,k6_lattices(sK6)) = k6_lattices(sK6)
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1420])).

cnf(c_1970,plain,
    ( k1_lattices(sK6,sK7,k6_lattices(sK6)) = k6_lattices(sK6) ),
    inference(superposition,[status(thm)],[c_1750,c_1752])).

cnf(c_30,plain,
    ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_lattices(X0)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_725,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_37])).

cnf(c_726,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_130,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_728,plain,
    ( v6_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_38,c_37,c_35,c_130])).

cnf(c_972,plain,
    ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_728])).

cnf(c_973,plain,
    ( r1_lattices(sK6,X0,k1_lattices(sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v5_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v9_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_972])).

cnf(c_4,plain,
    ( v5_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_127,plain,
    ( v5_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_136,plain,
    ( v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_139,plain,
    ( ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | v9_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_lattices(sK6,X0,k1_lattices(sK6,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_973,c_38,c_37,c_35,c_127,c_136,c_139])).

cnf(c_978,plain,
    ( r1_lattices(sK6,X0,k1_lattices(sK6,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_977])).

cnf(c_1414,plain,
    ( r1_lattices(sK6,X0_56,k1_lattices(sK6,X0_56,X1_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_978])).

cnf(c_1760,plain,
    ( r1_lattices(sK6,X0_56,k1_lattices(sK6,X0_56,X1_56)) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1414])).

cnf(c_3510,plain,
    ( r1_lattices(sK6,sK7,k6_lattices(sK6)) = iProver_top
    | m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1970,c_1760])).

cnf(c_3567,plain,
    ( r1_lattices(sK6,sK7,k6_lattices(sK6))
    | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3510])).

cnf(c_2,plain,
    ( v7_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_520,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

cnf(c_524,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_32,c_2,c_1,c_0])).

cnf(c_525,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_660,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_525,c_37])).

cnf(c_661,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | r1_lattices(sK6,k2_lattices(sK6,X0,X2),k2_lattices(sK6,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | r1_lattices(sK6,k2_lattices(sK6,X0,X2),k2_lattices(sK6,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_38,c_35])).

cnf(c_666,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | r1_lattices(sK6,k2_lattices(sK6,X0,X2),k2_lattices(sK6,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_1417,plain,
    ( ~ r1_lattices(sK6,X0_56,X1_56)
    | r1_lattices(sK6,k2_lattices(sK6,X0_56,X2_56),k2_lattices(sK6,X1_56,X2_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X2_56,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_666])).

cnf(c_3046,plain,
    ( ~ r1_lattices(sK6,X0_56,k6_lattices(sK6))
    | r1_lattices(sK6,k2_lattices(sK6,X0_56,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_3052,plain,
    ( r1_lattices(sK6,k2_lattices(sK6,sK7,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
    | ~ r1_lattices(sK6,sK7,k6_lattices(sK6))
    | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_1429,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_2698,plain,
    ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56) != X1_56
    | sK7 != X1_56
    | sK7 = k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_2699,plain,
    ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7) != sK7
    | sK7 = k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_23,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_20])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_487,c_38])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k2_lattices(sK6,X0,X1),u1_struct_0(sK6))
    | ~ l3_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1248,plain,
    ( m1_subset_1(k2_lattices(sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_35])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k2_lattices(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1248])).

cnf(c_1407,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | m1_subset_1(k2_lattices(sK6,X0_56,X1_56),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1249])).

cnf(c_2315,plain,
    ( m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_2280,plain,
    ( k2_lattices(sK6,X0_56,sK7) != X1_56
    | sK7 != X1_56
    | sK7 = k2_lattices(sK6,X0_56,sK7) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_2281,plain,
    ( k2_lattices(sK6,sK7,sK7) != sK7
    | sK7 = k2_lattices(sK6,sK7,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(X0_56,X0_57)
    | m1_subset_1(X1_56,X0_57)
    | X1_56 != X0_56 ),
    theory(equality)).

cnf(c_1927,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(k2_lattices(sK6,X1_56,X2_56),u1_struct_0(sK6))
    | X0_56 != k2_lattices(sK6,X1_56,X2_56) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1974,plain,
    ( m1_subset_1(k4_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k2_lattices(sK6,X0_56,X1_56),u1_struct_0(sK6))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,X0_56,X1_56) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2272,plain,
    ( m1_subset_1(k4_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_2118,plain,
    ( r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_2124,plain,
    ( r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7))
    | ~ m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_1944,plain,
    ( ~ r1_lattices(sK6,X0_56,X1_56)
    | r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != X0_56
    | sK7 != X1_56 ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_2002,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
    | ~ r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56)
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
    | sK7 != X0_56 ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_2117,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
    | ~ r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
    | sK7 != k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56) ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_2120,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
    | ~ r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
    | sK7 != k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_778,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_1202,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_778,c_38])).

cnf(c_1203,plain,
    ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ l3_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_1202])).

cnf(c_1205,plain,
    ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_38,c_35,c_75,c_78])).

cnf(c_1409,plain,
    ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1205])).

cnf(c_1765,plain,
    ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_1264])).

cnf(c_736,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_37])).

cnf(c_737,plain,
    ( v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_739,plain,
    ( v8_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_38,c_37,c_35,c_136])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_739])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_1269,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_38,c_35,c_1153])).

cnf(c_1410,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X0_56,X1_56),X1_56) = X1_56 ),
    inference(subtyping,[status(esa)],[c_1269])).

cnf(c_1764,plain,
    ( k1_lattices(sK6,k2_lattices(sK6,X0_56,X1_56),X1_56) = X1_56
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1410])).

cnf(c_2045,plain,
    ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),X0_56),X0_56) = X0_56
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1764])).

cnf(c_2056,plain,
    ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7) = sK7
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_5,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_418,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_5,c_31])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X2,X1)
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_22])).

cnf(c_423,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_687,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_423,c_37])).

cnf(c_688,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ r1_lattices(sK6,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_692,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ r1_lattices(sK6,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_38,c_35])).

cnf(c_693,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ r1_lattices(sK6,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_692])).

cnf(c_1416,plain,
    ( ~ r1_lattices(sK6,X0_56,X1_56)
    | ~ r1_lattices(sK6,X1_56,X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | X1_56 = X0_56 ),
    inference(subtyping,[status(esa)],[c_693])).

cnf(c_1989,plain,
    ( ~ r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
    | ~ r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
    | ~ m1_subset_1(k4_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | sK7 = k4_lattices(sK6,k6_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_1428,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_1955,plain,
    ( k4_lattices(sK6,k6_lattices(sK6),sK7) = k4_lattices(sK6,k6_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_1920,plain,
    ( k4_lattices(sK6,k6_lattices(sK6),sK7) != X0_56
    | k4_lattices(sK6,k6_lattices(sK6),sK7) = sK7
    | sK7 != X0_56 ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_1954,plain,
    ( k4_lattices(sK6,k6_lattices(sK6),sK7) != k4_lattices(sK6,k6_lattices(sK6),sK7)
    | k4_lattices(sK6,k6_lattices(sK6),sK7) = sK7
    | sK7 != k4_lattices(sK6,k6_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_24])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_463,c_728])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | k4_lattices(sK6,X0,X1) = k2_lattices(sK6,X0,X1) ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_998,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k4_lattices(sK6,X0,X1) = k2_lattices(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_994,c_38,c_35])).

cnf(c_1413,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | k4_lattices(sK6,X0_56,X1_56) = k2_lattices(sK6,X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_998])).

cnf(c_1948,plain,
    ( ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | k4_lattices(sK6,k6_lattices(sK6),sK7) = k2_lattices(sK6,k6_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_29,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_747,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_37])).

cnf(c_748,plain,
    ( ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | v9_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_750,plain,
    ( v9_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_38,c_37,c_35,c_139])).

cnf(c_1026,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_750])).

cnf(c_1027,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1026])).

cnf(c_1031,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_lattices(sK6,X0,X1)
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1027,c_38,c_37,c_35,c_136])).

cnf(c_1032,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1031])).

cnf(c_1412,plain,
    ( ~ r1_lattices(sK6,X0_56,X1_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | k2_lattices(sK6,X0_56,X1_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_1032])).

cnf(c_1471,plain,
    ( ~ r1_lattices(sK6,sK7,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | k2_lattices(sK6,sK7,sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_26,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_27,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_912,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ v6_lattices(X0)
    | ~ v6_lattices(X4)
    | ~ v8_lattices(X0)
    | ~ v8_lattices(X4)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v9_lattices(X0)
    | ~ v9_lattices(X4)
    | X3 != X2
    | X3 != X1
    | X4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_27])).

cnf(c_913,plain,
    ( r1_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_951,plain,
    ( r1_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_913,c_728])).

cnf(c_952,plain,
    ( r1_lattices(sK6,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v9_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_956,plain,
    ( r1_lattices(sK6,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_38,c_37,c_35,c_136,c_139])).

cnf(c_957,plain,
    ( r1_lattices(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_956])).

cnf(c_1415,plain,
    ( r1_lattices(sK6,X0_56,X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_957])).

cnf(c_1424,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1415])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_1425,plain,
    ( r1_lattices(sK6,X0_56,X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1415])).

cnf(c_1459,plain,
    ( r1_lattices(sK6,sK7,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_1426,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1415])).

cnf(c_33,negated_conjecture,
    ( k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1423,negated_conjecture,
    ( k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1439,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6187,c_3567,c_3052,c_2699,c_2315,c_2281,c_2272,c_2124,c_2120,c_2056,c_1989,c_1955,c_1954,c_1948,c_1471,c_1462,c_1459,c_1426,c_1423,c_1439,c_78,c_75,c_43,c_34,c_35,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/0.99  
% 2.58/0.99  ------  iProver source info
% 2.58/0.99  
% 2.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/0.99  git: non_committed_changes: false
% 2.58/0.99  git: last_make_outside_of_git: false
% 2.58/0.99  
% 2.58/0.99  ------ 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options
% 2.58/0.99  
% 2.58/0.99  --out_options                           all
% 2.58/0.99  --tptp_safe_out                         true
% 2.58/0.99  --problem_path                          ""
% 2.58/0.99  --include_path                          ""
% 2.58/0.99  --clausifier                            res/vclausify_rel
% 2.58/0.99  --clausifier_options                    --mode clausify
% 2.58/0.99  --stdin                                 false
% 2.58/0.99  --stats_out                             all
% 2.58/0.99  
% 2.58/0.99  ------ General Options
% 2.58/0.99  
% 2.58/0.99  --fof                                   false
% 2.58/0.99  --time_out_real                         305.
% 2.58/0.99  --time_out_virtual                      -1.
% 2.58/0.99  --symbol_type_check                     false
% 2.58/0.99  --clausify_out                          false
% 2.58/0.99  --sig_cnt_out                           false
% 2.58/0.99  --trig_cnt_out                          false
% 2.58/0.99  --trig_cnt_out_tolerance                1.
% 2.58/0.99  --trig_cnt_out_sk_spl                   false
% 2.58/0.99  --abstr_cl_out                          false
% 2.58/0.99  
% 2.58/0.99  ------ Global Options
% 2.58/0.99  
% 2.58/0.99  --schedule                              default
% 2.58/0.99  --add_important_lit                     false
% 2.58/0.99  --prop_solver_per_cl                    1000
% 2.58/0.99  --min_unsat_core                        false
% 2.58/0.99  --soft_assumptions                      false
% 2.58/0.99  --soft_lemma_size                       3
% 2.58/0.99  --prop_impl_unit_size                   0
% 2.58/0.99  --prop_impl_unit                        []
% 2.58/0.99  --share_sel_clauses                     true
% 2.58/0.99  --reset_solvers                         false
% 2.58/0.99  --bc_imp_inh                            [conj_cone]
% 2.58/0.99  --conj_cone_tolerance                   3.
% 2.58/0.99  --extra_neg_conj                        none
% 2.58/0.99  --large_theory_mode                     true
% 2.58/0.99  --prolific_symb_bound                   200
% 2.58/0.99  --lt_threshold                          2000
% 2.58/0.99  --clause_weak_htbl                      true
% 2.58/0.99  --gc_record_bc_elim                     false
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing Options
% 2.58/0.99  
% 2.58/0.99  --preprocessing_flag                    true
% 2.58/0.99  --time_out_prep_mult                    0.1
% 2.58/0.99  --splitting_mode                        input
% 2.58/0.99  --splitting_grd                         true
% 2.58/0.99  --splitting_cvd                         false
% 2.58/0.99  --splitting_cvd_svl                     false
% 2.58/0.99  --splitting_nvd                         32
% 2.58/0.99  --sub_typing                            true
% 2.58/0.99  --prep_gs_sim                           true
% 2.58/0.99  --prep_unflatten                        true
% 2.58/0.99  --prep_res_sim                          true
% 2.58/0.99  --prep_upred                            true
% 2.58/0.99  --prep_sem_filter                       exhaustive
% 2.58/0.99  --prep_sem_filter_out                   false
% 2.58/0.99  --pred_elim                             true
% 2.58/0.99  --res_sim_input                         true
% 2.58/0.99  --eq_ax_congr_red                       true
% 2.58/0.99  --pure_diseq_elim                       true
% 2.58/0.99  --brand_transform                       false
% 2.58/0.99  --non_eq_to_eq                          false
% 2.58/0.99  --prep_def_merge                        true
% 2.58/0.99  --prep_def_merge_prop_impl              false
% 2.58/0.99  --prep_def_merge_mbd                    true
% 2.58/0.99  --prep_def_merge_tr_red                 false
% 2.58/0.99  --prep_def_merge_tr_cl                  false
% 2.58/0.99  --smt_preprocessing                     true
% 2.58/0.99  --smt_ac_axioms                         fast
% 2.58/0.99  --preprocessed_out                      false
% 2.58/0.99  --preprocessed_stats                    false
% 2.58/0.99  
% 2.58/0.99  ------ Abstraction refinement Options
% 2.58/0.99  
% 2.58/0.99  --abstr_ref                             []
% 2.58/0.99  --abstr_ref_prep                        false
% 2.58/0.99  --abstr_ref_until_sat                   false
% 2.58/0.99  --abstr_ref_sig_restrict                funpre
% 2.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.99  --abstr_ref_under                       []
% 2.58/0.99  
% 2.58/0.99  ------ SAT Options
% 2.58/0.99  
% 2.58/0.99  --sat_mode                              false
% 2.58/0.99  --sat_fm_restart_options                ""
% 2.58/0.99  --sat_gr_def                            false
% 2.58/0.99  --sat_epr_types                         true
% 2.58/0.99  --sat_non_cyclic_types                  false
% 2.58/0.99  --sat_finite_models                     false
% 2.58/0.99  --sat_fm_lemmas                         false
% 2.58/0.99  --sat_fm_prep                           false
% 2.58/0.99  --sat_fm_uc_incr                        true
% 2.58/0.99  --sat_out_model                         small
% 2.58/0.99  --sat_out_clauses                       false
% 2.58/0.99  
% 2.58/0.99  ------ QBF Options
% 2.58/0.99  
% 2.58/0.99  --qbf_mode                              false
% 2.58/0.99  --qbf_elim_univ                         false
% 2.58/0.99  --qbf_dom_inst                          none
% 2.58/0.99  --qbf_dom_pre_inst                      false
% 2.58/0.99  --qbf_sk_in                             false
% 2.58/0.99  --qbf_pred_elim                         true
% 2.58/0.99  --qbf_split                             512
% 2.58/0.99  
% 2.58/0.99  ------ BMC1 Options
% 2.58/0.99  
% 2.58/0.99  --bmc1_incremental                      false
% 2.58/0.99  --bmc1_axioms                           reachable_all
% 2.58/0.99  --bmc1_min_bound                        0
% 2.58/0.99  --bmc1_max_bound                        -1
% 2.58/0.99  --bmc1_max_bound_default                -1
% 2.58/0.99  --bmc1_symbol_reachability              true
% 2.58/0.99  --bmc1_property_lemmas                  false
% 2.58/0.99  --bmc1_k_induction                      false
% 2.58/0.99  --bmc1_non_equiv_states                 false
% 2.58/0.99  --bmc1_deadlock                         false
% 2.58/0.99  --bmc1_ucm                              false
% 2.58/0.99  --bmc1_add_unsat_core                   none
% 2.58/0.99  --bmc1_unsat_core_children              false
% 2.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.99  --bmc1_out_stat                         full
% 2.58/0.99  --bmc1_ground_init                      false
% 2.58/0.99  --bmc1_pre_inst_next_state              false
% 2.58/0.99  --bmc1_pre_inst_state                   false
% 2.58/0.99  --bmc1_pre_inst_reach_state             false
% 2.58/0.99  --bmc1_out_unsat_core                   false
% 2.58/0.99  --bmc1_aig_witness_out                  false
% 2.58/0.99  --bmc1_verbose                          false
% 2.58/0.99  --bmc1_dump_clauses_tptp                false
% 2.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.99  --bmc1_dump_file                        -
% 2.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.99  --bmc1_ucm_extend_mode                  1
% 2.58/0.99  --bmc1_ucm_init_mode                    2
% 2.58/0.99  --bmc1_ucm_cone_mode                    none
% 2.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.99  --bmc1_ucm_relax_model                  4
% 2.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.99  --bmc1_ucm_layered_model                none
% 2.58/0.99  --bmc1_ucm_max_lemma_size               10
% 2.58/0.99  
% 2.58/0.99  ------ AIG Options
% 2.58/0.99  
% 2.58/0.99  --aig_mode                              false
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation Options
% 2.58/0.99  
% 2.58/0.99  --instantiation_flag                    true
% 2.58/0.99  --inst_sos_flag                         false
% 2.58/0.99  --inst_sos_phase                        true
% 2.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel_side                     num_symb
% 2.58/0.99  --inst_solver_per_active                1400
% 2.58/0.99  --inst_solver_calls_frac                1.
% 2.58/0.99  --inst_passive_queue_type               priority_queues
% 2.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.99  --inst_passive_queues_freq              [25;2]
% 2.58/0.99  --inst_dismatching                      true
% 2.58/0.99  --inst_eager_unprocessed_to_passive     true
% 2.58/0.99  --inst_prop_sim_given                   true
% 2.58/0.99  --inst_prop_sim_new                     false
% 2.58/0.99  --inst_subs_new                         false
% 2.58/0.99  --inst_eq_res_simp                      false
% 2.58/0.99  --inst_subs_given                       false
% 2.58/0.99  --inst_orphan_elimination               true
% 2.58/0.99  --inst_learning_loop_flag               true
% 2.58/0.99  --inst_learning_start                   3000
% 2.58/0.99  --inst_learning_factor                  2
% 2.58/0.99  --inst_start_prop_sim_after_learn       3
% 2.58/0.99  --inst_sel_renew                        solver
% 2.58/0.99  --inst_lit_activity_flag                true
% 2.58/0.99  --inst_restr_to_given                   false
% 2.58/0.99  --inst_activity_threshold               500
% 2.58/0.99  --inst_out_proof                        true
% 2.58/0.99  
% 2.58/0.99  ------ Resolution Options
% 2.58/0.99  
% 2.58/0.99  --resolution_flag                       true
% 2.58/0.99  --res_lit_sel                           adaptive
% 2.58/0.99  --res_lit_sel_side                      none
% 2.58/0.99  --res_ordering                          kbo
% 2.58/0.99  --res_to_prop_solver                    active
% 2.58/0.99  --res_prop_simpl_new                    false
% 2.58/0.99  --res_prop_simpl_given                  true
% 2.58/0.99  --res_passive_queue_type                priority_queues
% 2.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.99  --res_passive_queues_freq               [15;5]
% 2.58/0.99  --res_forward_subs                      full
% 2.58/0.99  --res_backward_subs                     full
% 2.58/0.99  --res_forward_subs_resolution           true
% 2.58/0.99  --res_backward_subs_resolution          true
% 2.58/0.99  --res_orphan_elimination                true
% 2.58/0.99  --res_time_limit                        2.
% 2.58/0.99  --res_out_proof                         true
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Options
% 2.58/0.99  
% 2.58/0.99  --superposition_flag                    true
% 2.58/0.99  --sup_passive_queue_type                priority_queues
% 2.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.99  --demod_completeness_check              fast
% 2.58/0.99  --demod_use_ground                      true
% 2.58/0.99  --sup_to_prop_solver                    passive
% 2.58/0.99  --sup_prop_simpl_new                    true
% 2.58/0.99  --sup_prop_simpl_given                  true
% 2.58/0.99  --sup_fun_splitting                     false
% 2.58/0.99  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  ------ Parsing...
% 2.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.00  ------ Proving...
% 2.58/1.00  ------ Problem Properties 
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  clauses                                 19
% 2.58/1.00  conjectures                             2
% 2.58/1.00  EPR                                     1
% 2.58/1.00  Horn                                    17
% 2.58/1.00  unary                                   3
% 2.58/1.00  binary                                  4
% 2.58/1.00  lits                                    55
% 2.58/1.00  lits eq                                 13
% 2.58/1.00  fd_pure                                 0
% 2.58/1.00  fd_pseudo                               0
% 2.58/1.00  fd_cond                                 2
% 2.58/1.00  fd_pseudo_cond                          1
% 2.58/1.00  AC symbols                              0
% 2.58/1.00  
% 2.58/1.00  ------ Schedule dynamic 5 is on 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  Current options:
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     none
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       false
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ Proving...
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS status Theorem for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  fof(f15,conjecture,(
% 2.58/1.00    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f16,negated_conjecture,(
% 2.58/1.00    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 2.58/1.00    inference(negated_conjecture,[],[f15])).
% 2.58/1.00  
% 2.58/1.00  fof(f44,plain,(
% 2.58/1.00    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f16])).
% 2.58/1.00  
% 2.58/1.00  fof(f45,plain,(
% 2.58/1.00    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f44])).
% 2.58/1.00  
% 2.58/1.00  fof(f64,plain,(
% 2.58/1.00    ( ! [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) => (k4_lattices(X0,k6_lattices(X0),sK7) != sK7 & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f63,plain,(
% 2.58/1.00    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k4_lattices(sK6,k6_lattices(sK6),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK6))) & l3_lattices(sK6) & v14_lattices(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f65,plain,(
% 2.58/1.00    (k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7 & m1_subset_1(sK7,u1_struct_0(sK6))) & l3_lattices(sK6) & v14_lattices(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f45,f64,f63])).
% 2.58/1.00  
% 2.58/1.00  fof(f103,plain,(
% 2.58/1.00    m1_subset_1(sK7,u1_struct_0(sK6))),
% 2.58/1.00    inference(cnf_transformation,[],[f65])).
% 2.58/1.00  
% 2.58/1.00  fof(f2,axiom,(
% 2.58/1.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f19,plain,(
% 2.58/1.00    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f2])).
% 2.58/1.00  
% 2.58/1.00  fof(f20,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f19])).
% 2.58/1.00  
% 2.58/1.00  fof(f46,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(nnf_transformation,[],[f20])).
% 2.58/1.00  
% 2.58/1.00  fof(f47,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(rectify,[],[f46])).
% 2.58/1.00  
% 2.58/1.00  fof(f48,plain,(
% 2.58/1.00    ! [X1,X0] : (? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k1_lattices(X0,sK0(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f49,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ((k1_lattices(X0,sK0(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 2.58/1.00  
% 2.58/1.00  fof(f74,plain,(
% 2.58/1.00    ( ! [X0,X3,X1] : (k1_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f49])).
% 2.58/1.00  
% 2.58/1.00  fof(f105,plain,(
% 2.58/1.00    ( ! [X0,X3] : (k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(equality_resolution,[],[f74])).
% 2.58/1.00  
% 2.58/1.00  fof(f101,plain,(
% 2.58/1.00    v14_lattices(sK6)),
% 2.58/1.00    inference(cnf_transformation,[],[f65])).
% 2.58/1.00  
% 2.58/1.00  fof(f99,plain,(
% 2.58/1.00    ~v2_struct_0(sK6)),
% 2.58/1.00    inference(cnf_transformation,[],[f65])).
% 2.58/1.00  
% 2.58/1.00  fof(f102,plain,(
% 2.58/1.00    l3_lattices(sK6)),
% 2.58/1.00    inference(cnf_transformation,[],[f65])).
% 2.58/1.00  
% 2.58/1.00  fof(f7,axiom,(
% 2.58/1.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f29,plain,(
% 2.58/1.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f7])).
% 2.58/1.00  
% 2.58/1.00  fof(f89,plain,(
% 2.58/1.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f29])).
% 2.58/1.00  
% 2.58/1.00  fof(f6,axiom,(
% 2.58/1.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f27,plain,(
% 2.58/1.00    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f6])).
% 2.58/1.00  
% 2.58/1.00  fof(f28,plain,(
% 2.58/1.00    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f27])).
% 2.58/1.00  
% 2.58/1.00  fof(f87,plain,(
% 2.58/1.00    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f28])).
% 2.58/1.00  
% 2.58/1.00  fof(f12,axiom,(
% 2.58/1.00    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f38,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f12])).
% 2.58/1.00  
% 2.58/1.00  fof(f39,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f38])).
% 2.58/1.00  
% 2.58/1.00  fof(f96,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f39])).
% 2.58/1.00  
% 2.58/1.00  fof(f1,axiom,(
% 2.58/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f17,plain,(
% 2.58/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f1])).
% 2.58/1.00  
% 2.58/1.00  fof(f18,plain,(
% 2.58/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.58/1.00    inference(flattening,[],[f17])).
% 2.58/1.00  
% 2.58/1.00  fof(f69,plain,(
% 2.58/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f100,plain,(
% 2.58/1.00    v10_lattices(sK6)),
% 2.58/1.00    inference(cnf_transformation,[],[f65])).
% 2.58/1.00  
% 2.58/1.00  fof(f68,plain,(
% 2.58/1.00    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f71,plain,(
% 2.58/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f72,plain,(
% 2.58/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f70,plain,(
% 2.58/1.00    ( ! [X0] : (v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f14,axiom,(
% 2.58/1.00    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f42,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f14])).
% 2.58/1.00  
% 2.58/1.00  fof(f43,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  fof(f98,plain,(
% 2.58/1.00    ( ! [X2,X0,X3,X1] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f43])).
% 2.58/1.00  
% 2.58/1.00  fof(f88,plain,(
% 2.58/1.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f29])).
% 2.58/1.00  
% 2.58/1.00  fof(f5,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f25,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f5])).
% 2.58/1.00  
% 2.58/1.00  fof(f26,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f25])).
% 2.58/1.00  
% 2.58/1.00  fof(f86,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f26])).
% 2.58/1.00  
% 2.58/1.00  fof(f4,axiom,(
% 2.58/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f23,plain,(
% 2.58/1.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f4])).
% 2.58/1.00  
% 2.58/1.00  fof(f24,plain,(
% 2.58/1.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f23])).
% 2.58/1.00  
% 2.58/1.00  fof(f56,plain,(
% 2.58/1.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(nnf_transformation,[],[f24])).
% 2.58/1.00  
% 2.58/1.00  fof(f57,plain,(
% 2.58/1.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(rectify,[],[f56])).
% 2.58/1.00  
% 2.58/1.00  fof(f59,plain,(
% 2.58/1.00    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK5(X0)),sK5(X0)) != sK5(X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))))) )),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f58,plain,(
% 2.58/1.00    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f60,plain,(
% 2.58/1.00    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) != sK5(X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f57,f59,f58])).
% 2.58/1.00  
% 2.58/1.00  fof(f82,plain,(
% 2.58/1.00    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f60])).
% 2.58/1.00  
% 2.58/1.00  fof(f67,plain,(
% 2.58/1.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f13,axiom,(
% 2.58/1.00    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f40,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f13])).
% 2.58/1.00  
% 2.58/1.00  fof(f41,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f40])).
% 2.58/1.00  
% 2.58/1.00  fof(f97,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f8,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f30,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f8])).
% 2.58/1.00  
% 2.58/1.00  fof(f31,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f30])).
% 2.58/1.00  
% 2.58/1.00  fof(f90,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f31])).
% 2.58/1.00  
% 2.58/1.00  fof(f11,axiom,(
% 2.58/1.00    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f36,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f11])).
% 2.58/1.00  
% 2.58/1.00  fof(f37,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f36])).
% 2.58/1.00  
% 2.58/1.00  fof(f62,plain,(
% 2.58/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(nnf_transformation,[],[f37])).
% 2.58/1.00  
% 2.58/1.00  fof(f94,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f62])).
% 2.58/1.00  
% 2.58/1.00  fof(f9,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f32,plain,(
% 2.58/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f9])).
% 2.58/1.00  
% 2.58/1.00  fof(f33,plain,(
% 2.58/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f32])).
% 2.58/1.00  
% 2.58/1.00  fof(f61,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(nnf_transformation,[],[f33])).
% 2.58/1.00  
% 2.58/1.00  fof(f91,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f61])).
% 2.58/1.00  
% 2.58/1.00  fof(f10,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f34,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.58/1.00    inference(ennf_transformation,[],[f10])).
% 2.58/1.00  
% 2.58/1.00  fof(f35,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.58/1.00    inference(flattening,[],[f34])).
% 2.58/1.00  
% 2.58/1.00  fof(f93,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f35])).
% 2.58/1.00  
% 2.58/1.00  fof(f104,plain,(
% 2.58/1.00    k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7),
% 2.58/1.00    inference(cnf_transformation,[],[f65])).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1433,plain,
% 2.58/1.00      ( ~ r1_lattices(X0_58,X0_56,X1_56)
% 2.58/1.00      | r1_lattices(X0_58,X2_56,X3_56)
% 2.58/1.00      | X2_56 != X0_56
% 2.58/1.00      | X3_56 != X1_56 ),
% 2.58/1.00      theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3217,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,X1_56)
% 2.58/1.00      | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != X1_56
% 2.58/1.00      | sK7 != X0_56 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1433]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3354,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,k2_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | sK7 != X0_56 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_3217]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_6179,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,k2_lattices(sK6,X0_56,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | sK7 != k2_lattices(sK6,X0_56,sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_3354]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_6187,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,k2_lattices(sK6,sK7,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | sK7 != k2_lattices(sK6,sK7,sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_6179]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_34,negated_conjecture,
% 2.58/1.00      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1422,negated_conjecture,
% 2.58/1.00      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_34]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1750,plain,
% 2.58/1.00      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1422]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
% 2.58/1.00      | ~ l2_lattices(X1)
% 2.58/1.00      | ~ v14_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_36,negated_conjecture,
% 2.58/1.00      ( v14_lattices(sK6) ),
% 2.58/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_582,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
% 2.58/1.00      | ~ l2_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
% 2.58/1.00      | sK6 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_36]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_583,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ l2_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | k1_lattices(sK6,X0,k6_lattices(sK6)) = k6_lattices(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_582]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_38,negated_conjecture,
% 2.58/1.00      ( ~ v2_struct_0(sK6) ),
% 2.58/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_35,negated_conjecture,
% 2.58/1.00      ( l3_lattices(sK6) ),
% 2.58/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_22,plain,
% 2.58/1.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_75,plain,
% 2.58/1.00      ( l2_lattices(sK6) | ~ l3_lattices(sK6) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_21,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 2.58/1.00      | ~ l2_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_78,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ l2_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_587,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | k1_lattices(sK6,X0,k6_lattices(sK6)) = k6_lattices(sK6) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_583,c_38,c_35,c_75,c_78]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1420,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | k1_lattices(sK6,X0_56,k6_lattices(sK6)) = k6_lattices(sK6) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_587]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1752,plain,
% 2.58/1.00      ( k1_lattices(sK6,X0_56,k6_lattices(sK6)) = k6_lattices(sK6)
% 2.58/1.00      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1420]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1970,plain,
% 2.58/1.00      ( k1_lattices(sK6,sK7,k6_lattices(sK6)) = k6_lattices(sK6) ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1750,c_1752]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_30,plain,
% 2.58/1.00      ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v5_lattices(X0)
% 2.58/1.00      | ~ v6_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3,plain,
% 2.58/1.00      ( v6_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_37,negated_conjecture,
% 2.58/1.00      ( v10_lattices(sK6) ),
% 2.58/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_725,plain,
% 2.58/1.00      ( v6_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_37]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_726,plain,
% 2.58/1.00      ( v6_lattices(sK6) | ~ l3_lattices(sK6) | v2_struct_0(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_725]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_130,plain,
% 2.58/1.00      ( v6_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | ~ v10_lattices(sK6) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_728,plain,
% 2.58/1.00      ( v6_lattices(sK6) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_726,c_38,c_37,c_35,c_130]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_972,plain,
% 2.58/1.00      ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v5_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_728]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_973,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0,k1_lattices(sK6,X0,X1))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ v5_lattices(sK6)
% 2.58/1.00      | ~ v8_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | ~ v9_lattices(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_972]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_4,plain,
% 2.58/1.00      ( v5_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_127,plain,
% 2.58/1.00      ( v5_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | ~ v10_lattices(sK6) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1,plain,
% 2.58/1.00      ( v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_136,plain,
% 2.58/1.00      ( v8_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | ~ v10_lattices(sK6) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_0,plain,
% 2.58/1.00      ( ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0)
% 2.58/1.00      | v9_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_139,plain,
% 2.58/1.00      ( ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | ~ v10_lattices(sK6)
% 2.58/1.00      | v9_lattices(sK6) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_977,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | r1_lattices(sK6,X0,k1_lattices(sK6,X0,X1)) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_973,c_38,c_37,c_35,c_127,c_136,c_139]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_978,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0,k1_lattices(sK6,X0,X1))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_977]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1414,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0_56,k1_lattices(sK6,X0_56,X1_56))
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_978]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1760,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0_56,k1_lattices(sK6,X0_56,X1_56)) = iProver_top
% 2.58/1.00      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 2.58/1.00      | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1414]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3510,plain,
% 2.58/1.00      ( r1_lattices(sK6,sK7,k6_lattices(sK6)) = iProver_top
% 2.58/1.00      | m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) != iProver_top
% 2.58/1.00      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1970,c_1760]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3567,plain,
% 2.58/1.00      ( r1_lattices(sK6,sK7,k6_lattices(sK6))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3510]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2,plain,
% 2.58/1.00      ( v7_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_32,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v7_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_520,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0)
% 2.58/1.00      | ~ v9_lattices(X0) ),
% 2.58/1.00      inference(resolution,[status(thm)],[c_2,c_32]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_524,plain,
% 2.58/1.00      ( ~ v10_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_520,c_32,c_2,c_1,c_0]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_525,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0) ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_524]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_660,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_525,c_37]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_661,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | r1_lattices(sK6,k2_lattices(sK6,X0,X2),k2_lattices(sK6,X1,X2))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_660]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_665,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | r1_lattices(sK6,k2_lattices(sK6,X0,X2),k2_lattices(sK6,X1,X2))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_661,c_38,c_35]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_666,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | r1_lattices(sK6,k2_lattices(sK6,X0,X2),k2_lattices(sK6,X1,X2))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_665]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1417,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,X1_56)
% 2.58/1.00      | r1_lattices(sK6,k2_lattices(sK6,X0_56,X2_56),k2_lattices(sK6,X1_56,X2_56))
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X2_56,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_666]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3046,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,k6_lattices(sK6))
% 2.58/1.00      | r1_lattices(sK6,k2_lattices(sK6,X0_56,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1417]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3052,plain,
% 2.58/1.00      ( r1_lattices(sK6,k2_lattices(sK6,sK7,sK7),k2_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | ~ r1_lattices(sK6,sK7,k6_lattices(sK6))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_3046]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1429,plain,
% 2.58/1.00      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 2.58/1.00      theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2698,plain,
% 2.58/1.00      ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56) != X1_56
% 2.58/1.00      | sK7 != X1_56
% 2.58/1.00      | sK7 = k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2699,plain,
% 2.58/1.00      ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7) != sK7
% 2.58/1.00      | sK7 = k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7)
% 2.58/1.00      | sK7 != sK7 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2698]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_23,plain,
% 2.58/1.00      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_20,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 2.58/1.00      | ~ l1_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_486,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 2.58/1.00      | ~ l3_lattices(X3)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | X1 != X3 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_20]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_487,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1243,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | sK6 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_487,c_38]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1244,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | m1_subset_1(k2_lattices(sK6,X0,X1),u1_struct_0(sK6))
% 2.58/1.00      | ~ l3_lattices(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_1243]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1248,plain,
% 2.58/1.00      ( m1_subset_1(k2_lattices(sK6,X0,X1),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_1244,c_35]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1249,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | m1_subset_1(k2_lattices(sK6,X0,X1),u1_struct_0(sK6)) ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_1248]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1407,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 2.58/1.00      | m1_subset_1(k2_lattices(sK6,X0_56,X1_56),u1_struct_0(sK6)) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_1249]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2315,plain,
% 2.58/1.00      ( m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1407]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2280,plain,
% 2.58/1.00      ( k2_lattices(sK6,X0_56,sK7) != X1_56
% 2.58/1.00      | sK7 != X1_56
% 2.58/1.00      | sK7 = k2_lattices(sK6,X0_56,sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2281,plain,
% 2.58/1.00      ( k2_lattices(sK6,sK7,sK7) != sK7
% 2.58/1.00      | sK7 = k2_lattices(sK6,sK7,sK7)
% 2.58/1.00      | sK7 != sK7 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2280]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1431,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_56,X0_57)
% 2.58/1.00      | m1_subset_1(X1_56,X0_57)
% 2.58/1.00      | X1_56 != X0_56 ),
% 2.58/1.00      theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1927,plain,
% 2.58/1.00      ( m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k2_lattices(sK6,X1_56,X2_56),u1_struct_0(sK6))
% 2.58/1.00      | X0_56 != k2_lattices(sK6,X1_56,X2_56) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1431]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1974,plain,
% 2.58/1.00      ( m1_subset_1(k4_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k2_lattices(sK6,X0_56,X1_56),u1_struct_0(sK6))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,X0_56,X1_56) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1927]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2272,plain,
% 2.58/1.00      ( m1_subset_1(k4_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1974]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2118,plain,
% 2.58/1.00      ( r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56))
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1414]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2124,plain,
% 2.58/1.00      ( r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7))
% 2.58/1.00      | ~ m1_subset_1(k2_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2118]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1944,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,X1_56)
% 2.58/1.00      | r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != X0_56
% 2.58/1.00      | sK7 != X1_56 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1433]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2002,plain,
% 2.58/1.00      ( r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
% 2.58/1.00      | ~ r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56)
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | sK7 != X0_56 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1944]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2117,plain,
% 2.58/1.00      ( r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
% 2.58/1.00      | ~ r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | sK7 != k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),X0_56) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2002]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2120,plain,
% 2.58/1.00      ( r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
% 2.58/1.00      | ~ r1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) != k2_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | sK7 != k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2117]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_778,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0) ),
% 2.58/1.00      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1202,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_778,c_38]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1203,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ l3_lattices(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_1202]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1205,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_1203,c_38,c_35,c_75,c_78]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1409,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_1205]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1765,plain,
% 2.58/1.00      ( m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6)) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_19,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ v8_lattices(X1)
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
% 2.58/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1264,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ v8_lattices(X1)
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
% 2.58/1.00      | sK6 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1265,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ v8_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_1264]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_736,plain,
% 2.58/1.00      ( v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_37]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_737,plain,
% 2.58/1.00      ( v8_lattices(sK6) | ~ l3_lattices(sK6) | v2_struct_0(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_736]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_739,plain,
% 2.58/1.00      ( v8_lattices(sK6) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_737,c_38,c_37,c_35,c_136]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1152,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
% 2.58/1.00      | sK6 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_739]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1153,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_1152]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1269,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_1265,c_38,c_35,c_1153]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1410,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 2.58/1.00      | k1_lattices(sK6,k2_lattices(sK6,X0_56,X1_56),X1_56) = X1_56 ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_1269]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1764,plain,
% 2.58/1.00      ( k1_lattices(sK6,k2_lattices(sK6,X0_56,X1_56),X1_56) = X1_56
% 2.58/1.00      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 2.58/1.00      | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1410]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2045,plain,
% 2.58/1.00      ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),X0_56),X0_56) = X0_56
% 2.58/1.00      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_1765,c_1764]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2056,plain,
% 2.58/1.00      ( k1_lattices(sK6,k2_lattices(sK6,k6_lattices(sK6),sK7),sK7) = sK7
% 2.58/1.00      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2045]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_5,plain,
% 2.58/1.00      ( v4_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_31,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ r1_lattices(X0,X2,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ l2_lattices(X0)
% 2.58/1.00      | ~ v4_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | X2 = X1 ),
% 2.58/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_418,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ r1_lattices(X0,X2,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ l2_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0)
% 2.58/1.00      | X2 = X1 ),
% 2.58/1.00      inference(resolution,[status(thm)],[c_5,c_31]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_422,plain,
% 2.58/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ r1_lattices(X0,X2,X1)
% 2.58/1.00      | ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0)
% 2.58/1.00      | X2 = X1 ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_418,c_22]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_423,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ r1_lattices(X0,X2,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v10_lattices(X0)
% 2.58/1.00      | X2 = X1 ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_422]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_687,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ r1_lattices(X0,X2,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | X2 = X1
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_423,c_37]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_688,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | ~ r1_lattices(sK6,X1,X0)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | X1 = X0 ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_687]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_692,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | ~ r1_lattices(sK6,X1,X0)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | X1 = X0 ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_688,c_38,c_35]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_693,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | ~ r1_lattices(sK6,X1,X0)
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | X1 = X0 ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_692]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1416,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,X1_56)
% 2.58/1.00      | ~ r1_lattices(sK6,X1_56,X0_56)
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 2.58/1.00      | X1_56 = X0_56 ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_693]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1989,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,k4_lattices(sK6,k6_lattices(sK6),sK7),sK7)
% 2.58/1.00      | ~ r1_lattices(sK6,sK7,k4_lattices(sK6,k6_lattices(sK6),sK7))
% 2.58/1.00      | ~ m1_subset_1(k4_lattices(sK6,k6_lattices(sK6),sK7),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 2.58/1.00      | sK7 = k4_lattices(sK6,k6_lattices(sK6),sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1428,plain,( X0_56 = X0_56 ),theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1955,plain,
% 2.58/1.00      ( k4_lattices(sK6,k6_lattices(sK6),sK7) = k4_lattices(sK6,k6_lattices(sK6),sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1428]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1920,plain,
% 2.58/1.00      ( k4_lattices(sK6,k6_lattices(sK6),sK7) != X0_56
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) = sK7
% 2.58/1.00      | sK7 != X0_56 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1954,plain,
% 2.58/1.00      ( k4_lattices(sK6,k6_lattices(sK6),sK7) != k4_lattices(sK6,k6_lattices(sK6),sK7)
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) = sK7
% 2.58/1.00      | sK7 != k4_lattices(sK6,k6_lattices(sK6),sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1920]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_24,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ l1_lattices(X1)
% 2.58/1.00      | ~ v6_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 2.58/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_462,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ v6_lattices(X1)
% 2.58/1.00      | ~ l3_lattices(X3)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | X1 != X3
% 2.58/1.00      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_24]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_463,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ v6_lattices(X1)
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_462]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_993,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.58/1.00      | ~ l3_lattices(X1)
% 2.58/1.00      | v2_struct_0(X1)
% 2.58/1.00      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
% 2.58/1.00      | sK6 != X1 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_463,c_728]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_994,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | k4_lattices(sK6,X0,X1) = k2_lattices(sK6,X0,X1) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_993]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_998,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | k4_lattices(sK6,X0,X1) = k2_lattices(sK6,X0,X1) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_994,c_38,c_35]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1413,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 2.58/1.00      | k4_lattices(sK6,X0_56,X1_56) = k2_lattices(sK6,X0_56,X1_56) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_998]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1948,plain,
% 2.58/1.00      ( ~ m1_subset_1(k6_lattices(sK6),u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 2.58/1.00      | k4_lattices(sK6,k6_lattices(sK6),sK7) = k2_lattices(sK6,k6_lattices(sK6),sK7) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1413]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_29,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0)
% 2.58/1.00      | k2_lattices(X0,X1,X2) = X1 ),
% 2.58/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_747,plain,
% 2.58/1.00      ( ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | v9_lattices(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_37]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_748,plain,
% 2.58/1.00      ( ~ l3_lattices(sK6) | v2_struct_0(sK6) | v9_lattices(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_747]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_750,plain,
% 2.58/1.00      ( v9_lattices(sK6) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_748,c_38,c_37,c_35,c_139]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1026,plain,
% 2.58/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | k2_lattices(X0,X1,X2) = X1
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_750]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1027,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ v8_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | k2_lattices(sK6,X0,X1) = X0 ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_1026]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1031,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | k2_lattices(sK6,X0,X1) = X0 ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_1027,c_38,c_37,c_35,c_136]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1032,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0,X1)
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | k2_lattices(sK6,X0,X1) = X0 ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_1031]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1412,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,X0_56,X1_56)
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 2.58/1.00      | k2_lattices(sK6,X0_56,X1_56) = X0_56 ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_1032]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1471,plain,
% 2.58/1.00      ( ~ r1_lattices(sK6,sK7,sK7)
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 2.58/1.00      | k2_lattices(sK6,sK7,sK7) = sK7 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1412]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_26,plain,
% 2.58/1.00      ( r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ r3_lattices(X0,X1,X2)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v6_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_27,plain,
% 2.58/1.00      ( r3_lattices(X0,X1,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v6_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_912,plain,
% 2.58/1.00      ( r1_lattices(X0,X1,X2)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.58/1.00      | ~ m1_subset_1(X5,u1_struct_0(X4))
% 2.58/1.00      | ~ v6_lattices(X0)
% 2.58/1.00      | ~ v6_lattices(X4)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X4)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X4)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | v2_struct_0(X4)
% 2.58/1.00      | ~ v9_lattices(X0)
% 2.58/1.00      | ~ v9_lattices(X4)
% 2.58/1.00      | X3 != X2
% 2.58/1.00      | X3 != X1
% 2.58/1.00      | X4 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_27]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_913,plain,
% 2.58/1.00      ( r1_lattices(X0,X1,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v6_lattices(X0)
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_912]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_951,plain,
% 2.58/1.00      ( r1_lattices(X0,X1,X1)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.58/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.58/1.00      | ~ v8_lattices(X0)
% 2.58/1.00      | ~ l3_lattices(X0)
% 2.58/1.00      | v2_struct_0(X0)
% 2.58/1.00      | ~ v9_lattices(X0)
% 2.58/1.00      | sK6 != X0 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_913,c_728]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_952,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0,X0)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ v8_lattices(sK6)
% 2.58/1.00      | ~ l3_lattices(sK6)
% 2.58/1.00      | v2_struct_0(sK6)
% 2.58/1.00      | ~ v9_lattices(sK6) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_951]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_956,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0,X0)
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_952,c_38,c_37,c_35,c_136,c_139]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_957,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0,X0)
% 2.58/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(renaming,[status(thm)],[c_956]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1415,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0_56,X0_56)
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK6)) ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_957]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1424,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6)) | ~ sP0_iProver_split ),
% 2.58/1.00      inference(splitting,
% 2.58/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.58/1.00                [c_1415]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1462,plain,
% 2.58/1.00      ( ~ m1_subset_1(sK7,u1_struct_0(sK6)) | ~ sP0_iProver_split ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1424]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1425,plain,
% 2.58/1.00      ( r1_lattices(sK6,X0_56,X0_56)
% 2.58/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 2.58/1.00      | ~ sP1_iProver_split ),
% 2.58/1.00      inference(splitting,
% 2.58/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.58/1.00                [c_1415]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1459,plain,
% 2.58/1.00      ( r1_lattices(sK6,sK7,sK7)
% 2.58/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 2.58/1.00      | ~ sP1_iProver_split ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1425]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1426,plain,
% 2.58/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.58/1.00      inference(splitting,
% 2.58/1.00                [splitting(split),new_symbols(definition,[])],
% 2.58/1.00                [c_1415]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_33,negated_conjecture,
% 2.58/1.00      ( k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7 ),
% 2.58/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1423,negated_conjecture,
% 2.58/1.00      ( k4_lattices(sK6,k6_lattices(sK6),sK7) != sK7 ),
% 2.58/1.00      inference(subtyping,[status(esa)],[c_33]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1439,plain,
% 2.58/1.00      ( sK7 = sK7 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1428]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_43,plain,
% 2.58/1.00      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(contradiction,plain,
% 2.58/1.00      ( $false ),
% 2.58/1.00      inference(minisat,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_6187,c_3567,c_3052,c_2699,c_2315,c_2281,c_2272,c_2124,
% 2.58/1.00                 c_2120,c_2056,c_1989,c_1955,c_1954,c_1948,c_1471,c_1462,
% 2.58/1.00                 c_1459,c_1426,c_1423,c_1439,c_78,c_75,c_43,c_34,c_35,
% 2.58/1.00                 c_38]) ).
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  ------                               Statistics
% 2.58/1.00  
% 2.58/1.00  ------ General
% 2.58/1.00  
% 2.58/1.00  abstr_ref_over_cycles:                  0
% 2.58/1.00  abstr_ref_under_cycles:                 0
% 2.58/1.00  gc_basic_clause_elim:                   0
% 2.58/1.00  forced_gc_time:                         0
% 2.58/1.00  parsing_time:                           0.007
% 2.58/1.00  unif_index_cands_time:                  0.
% 2.58/1.00  unif_index_add_time:                    0.
% 2.58/1.00  orderings_time:                         0.
% 2.58/1.00  out_proof_time:                         0.015
% 2.58/1.00  total_time:                             0.183
% 2.58/1.00  num_of_symbols:                         61
% 2.58/1.00  num_of_terms:                           5832
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing
% 2.58/1.00  
% 2.58/1.00  num_of_splits:                          2
% 2.58/1.00  num_of_split_atoms:                     2
% 2.58/1.00  num_of_reused_defs:                     0
% 2.58/1.00  num_eq_ax_congr_red:                    35
% 2.58/1.00  num_of_sem_filtered_clauses:            3
% 2.58/1.00  num_of_subtypes:                        3
% 2.58/1.00  monotx_restored_types:                  0
% 2.58/1.00  sat_num_of_epr_types:                   0
% 2.58/1.00  sat_num_of_non_cyclic_types:            0
% 2.58/1.00  sat_guarded_non_collapsed_types:        1
% 2.58/1.00  num_pure_diseq_elim:                    0
% 2.58/1.00  simp_replaced_by:                       0
% 2.58/1.00  res_preprocessed:                       104
% 2.58/1.00  prep_upred:                             0
% 2.58/1.00  prep_unflattend:                        36
% 2.58/1.00  smt_new_axioms:                         0
% 2.58/1.00  pred_elim_cands:                        2
% 2.58/1.00  pred_elim:                              13
% 2.58/1.00  pred_elim_cl:                           21
% 2.58/1.00  pred_elim_cycles:                       16
% 2.58/1.00  merged_defs:                            0
% 2.58/1.00  merged_defs_ncl:                        0
% 2.58/1.00  bin_hyper_res:                          0
% 2.58/1.00  prep_cycles:                            4
% 2.58/1.00  pred_elim_time:                         0.012
% 2.58/1.00  splitting_time:                         0.
% 2.58/1.00  sem_filter_time:                        0.
% 2.58/1.00  monotx_time:                            0.
% 2.58/1.00  subtype_inf_time:                       0.001
% 2.58/1.00  
% 2.58/1.00  ------ Problem properties
% 2.58/1.00  
% 2.58/1.00  clauses:                                19
% 2.58/1.00  conjectures:                            2
% 2.58/1.00  epr:                                    1
% 2.58/1.00  horn:                                   17
% 2.58/1.00  ground:                                 4
% 2.58/1.00  unary:                                  3
% 2.58/1.00  binary:                                 4
% 2.58/1.00  lits:                                   55
% 2.58/1.00  lits_eq:                                13
% 2.58/1.00  fd_pure:                                0
% 2.58/1.00  fd_pseudo:                              0
% 2.58/1.00  fd_cond:                                2
% 2.58/1.00  fd_pseudo_cond:                         1
% 2.58/1.00  ac_symbols:                             0
% 2.58/1.00  
% 2.58/1.00  ------ Propositional Solver
% 2.58/1.00  
% 2.58/1.00  prop_solver_calls:                      30
% 2.58/1.00  prop_fast_solver_calls:                 1162
% 2.58/1.00  smt_solver_calls:                       0
% 2.58/1.00  smt_fast_solver_calls:                  0
% 2.58/1.00  prop_num_of_clauses:                    2233
% 2.58/1.00  prop_preprocess_simplified:             5445
% 2.58/1.00  prop_fo_subsumed:                       66
% 2.58/1.00  prop_solver_time:                       0.
% 2.58/1.00  smt_solver_time:                        0.
% 2.58/1.00  smt_fast_solver_time:                   0.
% 2.58/1.00  prop_fast_solver_time:                  0.
% 2.58/1.00  prop_unsat_core_time:                   0.
% 2.58/1.00  
% 2.58/1.00  ------ QBF
% 2.58/1.00  
% 2.58/1.00  qbf_q_res:                              0
% 2.58/1.00  qbf_num_tautologies:                    0
% 2.58/1.00  qbf_prep_cycles:                        0
% 2.58/1.00  
% 2.58/1.00  ------ BMC1
% 2.58/1.00  
% 2.58/1.00  bmc1_current_bound:                     -1
% 2.58/1.00  bmc1_last_solved_bound:                 -1
% 2.58/1.00  bmc1_unsat_core_size:                   -1
% 2.58/1.00  bmc1_unsat_core_parents_size:           -1
% 2.58/1.00  bmc1_merge_next_fun:                    0
% 2.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation
% 2.58/1.00  
% 2.58/1.00  inst_num_of_clauses:                    626
% 2.58/1.00  inst_num_in_passive:                    141
% 2.58/1.00  inst_num_in_active:                     279
% 2.58/1.00  inst_num_in_unprocessed:                205
% 2.58/1.00  inst_num_of_loops:                      350
% 2.58/1.00  inst_num_of_learning_restarts:          0
% 2.58/1.00  inst_num_moves_active_passive:          65
% 2.58/1.00  inst_lit_activity:                      0
% 2.58/1.00  inst_lit_activity_moves:                0
% 2.58/1.00  inst_num_tautologies:                   0
% 2.58/1.00  inst_num_prop_implied:                  0
% 2.58/1.00  inst_num_existing_simplified:           0
% 2.58/1.00  inst_num_eq_res_simplified:             0
% 2.58/1.00  inst_num_child_elim:                    0
% 2.58/1.00  inst_num_of_dismatching_blockings:      326
% 2.58/1.00  inst_num_of_non_proper_insts:           762
% 2.58/1.00  inst_num_of_duplicates:                 0
% 2.58/1.00  inst_inst_num_from_inst_to_res:         0
% 2.58/1.00  inst_dismatching_checking_time:         0.
% 2.58/1.00  
% 2.58/1.00  ------ Resolution
% 2.58/1.00  
% 2.58/1.00  res_num_of_clauses:                     0
% 2.58/1.00  res_num_in_passive:                     0
% 2.58/1.00  res_num_in_active:                      0
% 2.58/1.00  res_num_of_loops:                       108
% 2.58/1.00  res_forward_subset_subsumed:            80
% 2.58/1.00  res_backward_subset_subsumed:           0
% 2.58/1.00  res_forward_subsumed:                   0
% 2.58/1.00  res_backward_subsumed:                  0
% 2.58/1.00  res_forward_subsumption_resolution:     0
% 2.58/1.00  res_backward_subsumption_resolution:    0
% 2.58/1.00  res_clause_to_clause_subsumption:       540
% 2.58/1.00  res_orphan_elimination:                 0
% 2.58/1.00  res_tautology_del:                      46
% 2.58/1.00  res_num_eq_res_simplified:              0
% 2.58/1.00  res_num_sel_changes:                    0
% 2.58/1.00  res_moves_from_active_to_pass:          0
% 2.58/1.00  
% 2.58/1.00  ------ Superposition
% 2.58/1.00  
% 2.58/1.00  sup_time_total:                         0.
% 2.58/1.00  sup_time_generating:                    0.
% 2.58/1.00  sup_time_sim_full:                      0.
% 2.58/1.00  sup_time_sim_immed:                     0.
% 2.58/1.00  
% 2.58/1.00  sup_num_of_clauses:                     124
% 2.58/1.00  sup_num_in_active:                      58
% 2.58/1.00  sup_num_in_passive:                     66
% 2.58/1.00  sup_num_of_loops:                       68
% 2.58/1.00  sup_fw_superposition:                   112
% 2.58/1.00  sup_bw_superposition:                   20
% 2.58/1.00  sup_immediate_simplified:               13
% 2.58/1.00  sup_given_eliminated:                   0
% 2.58/1.00  comparisons_done:                       0
% 2.58/1.00  comparisons_avoided:                    6
% 2.58/1.00  
% 2.58/1.00  ------ Simplifications
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  sim_fw_subset_subsumed:                 6
% 2.58/1.00  sim_bw_subset_subsumed:                 1
% 2.58/1.00  sim_fw_subsumed:                        0
% 2.58/1.00  sim_bw_subsumed:                        0
% 2.58/1.00  sim_fw_subsumption_res:                 0
% 2.58/1.00  sim_bw_subsumption_res:                 0
% 2.58/1.00  sim_tautology_del:                      1
% 2.58/1.00  sim_eq_tautology_del:                   11
% 2.58/1.00  sim_eq_res_simp:                        0
% 2.58/1.00  sim_fw_demodulated:                     0
% 2.58/1.00  sim_bw_demodulated:                     9
% 2.58/1.00  sim_light_normalised:                   8
% 2.58/1.00  sim_joinable_taut:                      0
% 2.58/1.00  sim_joinable_simp:                      0
% 2.58/1.00  sim_ac_normalised:                      0
% 2.58/1.00  sim_smt_subsumption:                    0
% 2.58/1.00  
%------------------------------------------------------------------------------

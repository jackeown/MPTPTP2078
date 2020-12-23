%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:19 EST 2020

% Result     : Theorem 15.07s
% Output     : CNFRefutation 15.07s
% Verified   : 
% Statistics : Number of formulae       :  279 (7714 expanded)
%              Number of clauses        :  178 (1967 expanded)
%              Number of leaves         :   27 (1639 expanded)
%              Depth                    :   33
%              Number of atoms          : 1385 (53825 expanded)
%              Number of equality atoms :  350 (7070 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
              & k2_lattices(X0,sK2(X0),X4) = sK2(X0) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
                  & k2_lattices(X0,sK2(X0),X4) = sK2(X0) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f38,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0)
        | ~ l3_lattices(sK10)
        | ~ v13_lattices(sK10)
        | ~ v10_lattices(sK10)
        | v2_struct_0(sK10) )
      & l3_lattices(sK10)
      & v4_lattice3(sK10)
      & v10_lattices(sK10)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ( k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0)
      | ~ l3_lattices(sK10)
      | ~ v13_lattices(sK10)
      | ~ v10_lattices(sK10)
      | v2_struct_0(sK10) )
    & l3_lattices(sK10)
    & v4_lattice3(sK10)
    & v10_lattices(sK10)
    & ~ v2_struct_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f39,f72])).

fof(f114,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f73])).

fof(f117,plain,(
    l3_lattices(sK10) ),
    inference(cnf_transformation,[],[f73])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f67])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK9(X0)) != k2_lattices(X0,sK9(X0),X1)
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK8(X0)) != k2_lattices(X0,sK8(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK8(X0),sK9(X0)) != k2_lattices(X0,sK9(X0),sK8(X0))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f68,f70,f69])).

fof(f110,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f3,axiom,(
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

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f19])).

fof(f79,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f115,plain,(
    v10_lattices(sK10) ),
    inference(cnf_transformation,[],[f73])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_lattices(X0,X5,X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,X5,X4)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f60,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK6(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK6(X0,X4),X4)
        & m1_subset_1(sK6(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK5(X0,X2))
        & r4_lattice3(X0,sK5(X0,X2),X1)
        & m1_subset_1(sK5(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,sK4(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK4(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK5(X0,X2))
                & r4_lattice3(X0,sK5(X0,X2),sK4(X0))
                & m1_subset_1(sK5(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK4(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK6(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK6(X0,X4),X4)
              & m1_subset_1(sK6(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f57,f60,f59,f58])).

fof(f99,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK6(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f116,plain,(
    v4_lattice3(sK10) ),
    inference(cnf_transformation,[],[f73])).

fof(f81,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    ! [X6,X4,X0] :
      ( r1_lattices(X0,sK6(X0,X4),X6)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f119,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f76])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f122,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
        & r4_lattice3(X0,sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
                & r4_lattice3(X0,sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f64,f65])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK7(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
    ! [X4,X0] :
      ( r4_lattice3(X0,sK6(X0,X4),X4)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f118,plain,
    ( k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0)
    | ~ l3_lattices(sK10)
    | ~ v13_lattices(sK10)
    | ~ v10_lattices(sK10)
    | v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1376,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_44])).

cnf(c_1377,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | v13_lattices(sK10) ),
    inference(unflattening,[status(thm)],[c_1376])).

cnf(c_41,negated_conjecture,
    ( l3_lattices(sK10) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_13,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_123,plain,
    ( l1_lattices(sK10)
    | ~ l3_lattices(sK10) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1381,plain,
    ( m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1377,c_41,c_123])).

cnf(c_1382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(renaming,[status(thm)],[c_1381])).

cnf(c_3554,plain,
    ( m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10)) = iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_12,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1305,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_44])).

cnf(c_1306,plain,
    ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10))
    | ~ l1_lattices(sK10) ),
    inference(unflattening,[status(thm)],[c_1305])).

cnf(c_126,plain,
    ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | v2_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1308,plain,
    ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_44,c_41,c_123,c_126])).

cnf(c_3557,plain,
    ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1308])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_44])).

cnf(c_1317,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | ~ v6_lattices(sK10)
    | k2_lattices(sK10,X1,X0) = k2_lattices(sK10,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1316])).

cnf(c_6,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,negated_conjecture,
    ( v10_lattices(sK10) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_904,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_43])).

cnf(c_905,plain,
    ( v6_lattices(sK10)
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_142,plain,
    ( v6_lattices(sK10)
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10)
    | ~ v10_lattices(sK10) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_907,plain,
    ( v6_lattices(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_44,c_43,c_41,c_142])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_907])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | v2_struct_0(sK10)
    | k2_lattices(sK10,X1,X0) = k2_lattices(sK10,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_1320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | k2_lattices(sK10,X1,X0) = k2_lattices(sK10,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1317,c_44,c_41,c_123,c_1017])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | k2_lattices(sK10,X0,X1) = k2_lattices(sK10,X1,X0) ),
    inference(renaming,[status(thm)],[c_1320])).

cnf(c_3566,plain,
    ( k2_lattices(sK10,X0,X1) = k2_lattices(sK10,X1,X0)
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_5159,plain,
    ( k2_lattices(sK10,sK1(sK10,X0),X1) = k2_lattices(sK10,X1,sK1(sK10,X0))
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_3566])).

cnf(c_20821,plain,
    ( k2_lattices(sK10,sK1(sK10,X0),sK1(sK10,X1)) = k2_lattices(sK10,sK1(sK10,X1),sK1(sK10,X0))
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_5159])).

cnf(c_37767,plain,
    ( k2_lattices(sK10,sK1(sK10,k5_lattices(sK10)),sK1(sK10,X0)) = k2_lattices(sK10,sK1(sK10,X0),sK1(sK10,k5_lattices(sK10)))
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3557,c_20821])).

cnf(c_37839,plain,
    ( k2_lattices(sK10,sK1(sK10,sK1(sK10,X0)),sK1(sK10,k5_lattices(sK10))) = k2_lattices(sK10,sK1(sK10,k5_lattices(sK10)),sK1(sK10,sK1(sK10,X0)))
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_37767])).

cnf(c_38793,plain,
    ( k2_lattices(sK10,sK1(sK10,k5_lattices(sK10)),sK1(sK10,sK1(sK10,sK1(sK10,X0)))) = k2_lattices(sK10,sK1(sK10,sK1(sK10,sK1(sK10,X0))),sK1(sK10,k5_lattices(sK10)))
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_37839])).

cnf(c_30,plain,
    ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1058,plain,
    ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_1059,plain,
    ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
    | ~ v4_lattice3(sK10)
    | v2_struct_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1058])).

cnf(c_42,negated_conjecture,
    ( v4_lattice3(sK10) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1063,plain,
    ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1059,c_44,c_42])).

cnf(c_31038,plain,
    ( m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10)) ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_31039,plain,
    ( m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31038])).

cnf(c_3033,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3032,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5667,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_3033,c_3032])).

cnf(c_4,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_15,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_537,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_15])).

cnf(c_5,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_5])).

cnf(c_542,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_766,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_43])).

cnf(c_767,plain,
    ( ~ r1_lattices(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10)
    | k2_lattices(sK10,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_771,plain,
    ( ~ r1_lattices(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | k2_lattices(sK10,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_44,c_41])).

cnf(c_8301,plain,
    ( ~ r1_lattices(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | X0 = k2_lattices(sK10,X0,X1) ),
    inference(resolution,[status(thm)],[c_5667,c_771])).

cnf(c_5674,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | X2 != k2_lattices(sK10,X0,X1)
    | k2_lattices(sK10,X1,X0) = X2 ),
    inference(resolution,[status(thm)],[c_3033,c_1321])).

cnf(c_8547,plain,
    ( ~ r1_lattices(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | k2_lattices(sK10,X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_8301,c_5674])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_44])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0
    | k2_lattices(sK10,sK1(sK10,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1397])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0
    | k2_lattices(sK10,sK1(sK10,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1398,c_41,c_123])).

cnf(c_54032,plain,
    ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
    | v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0 ),
    inference(resolution,[status(thm)],[c_8547,c_1402])).

cnf(c_54181,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r1_lattices(sK10,X0,sK1(sK10,X0))
    | v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54032,c_1382])).

cnf(c_54182,plain,
    ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0 ),
    inference(renaming,[status(thm)],[c_54181])).

cnf(c_54506,plain,
    ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(resolution,[status(thm)],[c_54182,c_771])).

cnf(c_54523,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r1_lattices(sK10,X0,sK1(sK10,X0))
    | v13_lattices(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54506,c_41,c_123,c_1377])).

cnf(c_54524,plain,
    ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(renaming,[status(thm)],[c_54523])).

cnf(c_28,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK6(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1088,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK6(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_1089,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | r1_lattices(sK10,sK6(sK10,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ v4_lattice3(sK10)
    | v2_struct_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1088])).

cnf(c_1093,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | r1_lattices(sK10,sK6(sK10,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1089,c_44,c_42])).

cnf(c_54549,plain,
    ( ~ r4_lattice3(sK10,sK1(sK10,sK6(sK10,X0)),X0)
    | ~ m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
    | ~ m1_subset_1(sK1(sK10,sK6(sK10,X0)),u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(resolution,[status(thm)],[c_54524,c_1093])).

cnf(c_3826,plain,
    ( ~ m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
    | m1_subset_1(sK1(sK10,sK6(sK10,X0)),u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_55176,plain,
    ( ~ r4_lattice3(sK10,sK1(sK10,sK6(sK10,X0)),X0)
    | v13_lattices(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54549,c_44,c_42,c_1059,c_3826])).

cnf(c_3035,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_5769,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_3035,c_0])).

cnf(c_9756,plain,
    ( ~ r1_lattices(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r2_hidden(X0,k1_xboole_0)
    | r2_hidden(k2_lattices(sK10,X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5769,c_771])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3575,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4884,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3575])).

cnf(c_4890,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4884])).

cnf(c_10374,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9756,c_4890])).

cnf(c_22,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1163,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_41])).

cnf(c_1164,plain,
    ( r4_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | r2_hidden(sK3(sK10,X0,X1),X1)
    | v2_struct_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1163])).

cnf(c_1168,plain,
    ( r2_hidden(sK3(sK10,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | r4_lattice3(sK10,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1164,c_44])).

cnf(c_1169,plain,
    ( r4_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | r2_hidden(sK3(sK10,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_1168])).

cnf(c_10484,plain,
    ( r4_lattice3(sK10,X0,k1_xboole_0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
    inference(resolution,[status(thm)],[c_10374,c_1169])).

cnf(c_56902,plain,
    ( ~ m1_subset_1(sK1(sK10,sK6(sK10,k1_xboole_0)),u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(resolution,[status(thm)],[c_55176,c_10484])).

cnf(c_58627,plain,
    ( ~ m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10))
    | v13_lattices(sK10) ),
    inference(resolution,[status(thm)],[c_56902,c_1382])).

cnf(c_58628,plain,
    ( m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58627])).

cnf(c_59462,plain,
    ( v13_lattices(sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38793,c_31039,c_58628])).

cnf(c_20,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1291,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_44])).

cnf(c_1292,plain,
    ( m1_subset_1(sK2(sK10),u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | ~ v13_lattices(sK10) ),
    inference(unflattening,[status(thm)],[c_1291])).

cnf(c_1294,plain,
    ( m1_subset_1(sK2(sK10),u1_struct_0(sK10))
    | ~ v13_lattices(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1292,c_41,c_123])).

cnf(c_3558,plain,
    ( m1_subset_1(sK2(sK10),u1_struct_0(sK10)) = iProver_top
    | v13_lattices(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_3560,plain,
    ( r4_lattice3(sK10,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | r2_hidden(sK3(sK10,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_5195,plain,
    ( r4_lattice3(sK10,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_4884])).

cnf(c_5595,plain,
    ( r4_lattice3(sK10,sK2(sK10),k1_xboole_0) = iProver_top
    | v13_lattices(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3558,c_5195])).

cnf(c_3563,plain,
    ( r4_lattice3(sK10,X0,X1) != iProver_top
    | r1_lattices(sK10,sK6(sK10,X1),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_3572,plain,
    ( k2_lattices(sK10,X0,X1) = X0
    | r1_lattices(sK10,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_4559,plain,
    ( k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0)
    | r4_lattice3(sK10,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3563,c_3572])).

cnf(c_45,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( v4_lattice3(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1060,plain,
    ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) = iProver_top
    | v4_lattice3(sK10) != iProver_top
    | v2_struct_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_1602,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK10))
    | ~ m1_subset_1(X3,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | X0 != X2
    | k2_lattices(sK10,X3,X2) = X3
    | sK6(sK10,X1) != X3
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_771,c_1093])).

cnf(c_1603,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10))
    | k2_lattices(sK10,sK6(sK10,X1),X0) = sK6(sK10,X1) ),
    inference(unflattening,[status(thm)],[c_1602])).

cnf(c_1604,plain,
    ( k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0)
    | r4_lattice3(sK10,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1603])).

cnf(c_7822,plain,
    ( m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
    | r4_lattice3(sK10,X1,X0) != iProver_top
    | k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4559,c_45,c_47,c_1060,c_1604])).

cnf(c_7823,plain,
    ( k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0)
    | r4_lattice3(sK10,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7822])).

cnf(c_7831,plain,
    ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),sK2(sK10)) = sK6(sK10,k1_xboole_0)
    | m1_subset_1(sK2(sK10),u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5595,c_7823])).

cnf(c_48,plain,
    ( l3_lattices(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_101,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v13_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_103,plain,
    ( m1_subset_1(sK2(sK10),u1_struct_0(sK10)) = iProver_top
    | l1_lattices(sK10) != iProver_top
    | v13_lattices(sK10) != iProver_top
    | v2_struct_0(sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_122,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_124,plain,
    ( l1_lattices(sK10) = iProver_top
    | l3_lattices(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_8031,plain,
    ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),sK2(sK10)) = sK6(sK10,k1_xboole_0)
    | v13_lattices(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7831,c_45,c_48,c_103,c_124])).

cnf(c_59503,plain,
    ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),sK2(sK10)) = sK6(sK10,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_59462,c_8031])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_44])).

cnf(c_1356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | ~ v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK2(sK10)) = sK2(sK10) ),
    inference(unflattening,[status(thm)],[c_1355])).

cnf(c_1360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ v13_lattices(sK10)
    | k2_lattices(sK10,X0,sK2(sK10)) = sK2(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_41,c_123])).

cnf(c_3555,plain,
    ( k2_lattices(sK10,X0,sK2(sK10)) = sK2(sK10)
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_4339,plain,
    ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = sK2(sK10)
    | v13_lattices(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3557,c_3555])).

cnf(c_59510,plain,
    ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = sK2(sK10) ),
    inference(superposition,[status(thm)],[c_59462,c_4339])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_44])).

cnf(c_1422,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10))
    | ~ l1_lattices(sK10)
    | ~ v13_lattices(sK10)
    | k2_lattices(sK10,k5_lattices(sK10),X0) = k5_lattices(sK10) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1426,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ v13_lattices(sK10)
    | k2_lattices(sK10,k5_lattices(sK10),X0) = k5_lattices(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_44,c_41,c_123,c_126])).

cnf(c_3552,plain,
    ( k2_lattices(sK10,k5_lattices(sK10),X0) = k5_lattices(sK10)
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v13_lattices(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_3993,plain,
    ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = k5_lattices(sK10)
    | v13_lattices(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3558,c_3552])).

cnf(c_59512,plain,
    ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = k5_lattices(sK10) ),
    inference(superposition,[status(thm)],[c_59462,c_3993])).

cnf(c_59523,plain,
    ( sK2(sK10) = k5_lattices(sK10) ),
    inference(light_normalisation,[status(thm)],[c_59510,c_59512])).

cnf(c_59538,plain,
    ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),k5_lattices(sK10)) = sK6(sK10,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_59503,c_59523])).

cnf(c_3565,plain,
    ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_4340,plain,
    ( k2_lattices(sK10,sK6(sK10,X0),sK2(sK10)) = sK2(sK10)
    | v13_lattices(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3565,c_3555])).

cnf(c_59507,plain,
    ( k2_lattices(sK10,sK6(sK10,X0),sK2(sK10)) = sK2(sK10) ),
    inference(superposition,[status(thm)],[c_59462,c_4340])).

cnf(c_59532,plain,
    ( k2_lattices(sK10,sK6(sK10,X0),k5_lattices(sK10)) = k5_lattices(sK10) ),
    inference(light_normalisation,[status(thm)],[c_59507,c_59523])).

cnf(c_59539,plain,
    ( sK6(sK10,k1_xboole_0) = k5_lattices(sK10) ),
    inference(demodulation,[status(thm)],[c_59538,c_59532])).

cnf(c_32,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK7(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_856,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK7(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_43])).

cnf(c_857,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | r4_lattice3(sK10,sK7(sK10,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ v4_lattice3(sK10)
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10)
    | k15_lattice3(sK10,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | r4_lattice3(sK10,sK7(sK10,X1,X0),X1)
    | ~ r4_lattice3(sK10,X0,X1)
    | k15_lattice3(sK10,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_857,c_44,c_42,c_41])).

cnf(c_862,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | r4_lattice3(sK10,sK7(sK10,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | k15_lattice3(sK10,X1) = X0 ),
    inference(renaming,[status(thm)],[c_861])).

cnf(c_3568,plain,
    ( k15_lattice3(sK10,X0) = X1
    | r4_lattice3(sK10,X1,X0) != iProver_top
    | r4_lattice3(sK10,sK7(sK10,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_31,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK7(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_880,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK7(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_43])).

cnf(c_881,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ r1_lattices(sK10,X0,sK7(sK10,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ v4_lattice3(sK10)
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10)
    | k15_lattice3(sK10,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_885,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r1_lattices(sK10,X0,sK7(sK10,X1,X0))
    | ~ r4_lattice3(sK10,X0,X1)
    | k15_lattice3(sK10,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_44,c_42,c_41])).

cnf(c_886,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ r1_lattices(sK10,X0,sK7(sK10,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | k15_lattice3(sK10,X1) = X0 ),
    inference(renaming,[status(thm)],[c_885])).

cnf(c_3567,plain,
    ( k15_lattice3(sK10,X0) = X1
    | r4_lattice3(sK10,X1,X0) != iProver_top
    | r1_lattices(sK10,X1,sK7(sK10,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_4967,plain,
    ( k15_lattice3(sK10,X0) = sK6(sK10,X1)
    | r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1) != iProver_top
    | r4_lattice3(sK10,sK6(sK10,X1),X0) != iProver_top
    | m1_subset_1(sK7(sK10,X0,sK6(sK10,X1)),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3563,c_3567])).

cnf(c_1706,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ r4_lattice3(sK10,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X2,u1_struct_0(sK10))
    | sK7(sK10,X1,X0) != X2
    | k15_lattice3(sK10,X1) = X0
    | sK6(sK10,X3) != X0
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_886,c_1093])).

cnf(c_1707,plain,
    ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
    | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
    | ~ m1_subset_1(sK7(sK10,X0,sK6(sK10,X1)),u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10))
    | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
    inference(unflattening,[status(thm)],[c_1706])).

cnf(c_33,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK7(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_832,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK7(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_43])).

cnf(c_833,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | m1_subset_1(sK7(sK10,X1,X0),u1_struct_0(sK10))
    | ~ v4_lattice3(sK10)
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10)
    | k15_lattice3(sK10,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_837,plain,
    ( m1_subset_1(sK7(sK10,X1,X0),u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r4_lattice3(sK10,X0,X1)
    | k15_lattice3(sK10,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_44,c_42,c_41])).

cnf(c_838,plain,
    ( ~ r4_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | m1_subset_1(sK7(sK10,X1,X0),u1_struct_0(sK10))
    | k15_lattice3(sK10,X1) = X0 ),
    inference(renaming,[status(thm)],[c_837])).

cnf(c_1721,plain,
    ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
    | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
    | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1707,c_1063,c_838])).

cnf(c_1725,plain,
    ( k15_lattice3(sK10,X0) = sK6(sK10,X1)
    | r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1) != iProver_top
    | r4_lattice3(sK10,sK6(sK10,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_10047,plain,
    ( k15_lattice3(sK10,X0) = sK6(sK10,X1)
    | r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1) != iProver_top
    | r4_lattice3(sK10,sK6(sK10,X1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4967,c_1725])).

cnf(c_10054,plain,
    ( k15_lattice3(sK10,X0) = sK6(sK10,X0)
    | r4_lattice3(sK10,sK6(sK10,X0),X0) != iProver_top
    | m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3568,c_10047])).

cnf(c_29,plain,
    ( r4_lattice3(X0,sK6(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1073,plain,
    ( r4_lattice3(X0,sK6(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_1074,plain,
    ( r4_lattice3(sK10,sK6(sK10,X0),X0)
    | ~ v4_lattice3(sK10)
    | v2_struct_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1073])).

cnf(c_4591,plain,
    ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
    | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
    | ~ m1_subset_1(sK7(sK10,X0,sK6(sK10,X1)),u1_struct_0(sK10))
    | ~ m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10))
    | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
    inference(resolution,[status(thm)],[c_886,c_1093])).

cnf(c_5130,plain,
    ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
    | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
    | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4591,c_1721])).

cnf(c_5207,plain,
    ( ~ r4_lattice3(sK10,sK6(sK10,X0),X0)
    | ~ m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
    | k15_lattice3(sK10,X0) = sK6(sK10,X0) ),
    inference(resolution,[status(thm)],[c_5130,c_862])).

cnf(c_10274,plain,
    ( k15_lattice3(sK10,X0) = sK6(sK10,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10054,c_44,c_42,c_1059,c_1074,c_5207])).

cnf(c_40,negated_conjecture,
    ( ~ v13_lattices(sK10)
    | ~ l3_lattices(sK10)
    | v2_struct_0(sK10)
    | ~ v10_lattices(sK10)
    | k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_245,negated_conjecture,
    ( ~ v13_lattices(sK10)
    | k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40,c_44,c_43,c_41])).

cnf(c_3574,plain,
    ( k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0)
    | v13_lattices(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_10277,plain,
    ( sK6(sK10,k1_xboole_0) != k5_lattices(sK10)
    | v13_lattices(sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10274,c_3574])).

cnf(c_10336,plain,
    ( ~ v13_lattices(sK10)
    | sK6(sK10,k1_xboole_0) != k5_lattices(sK10) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10277])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59539,c_58627,c_31038,c_10336])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 15.07/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.07/2.51  
% 15.07/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.07/2.51  
% 15.07/2.51  ------  iProver source info
% 15.07/2.51  
% 15.07/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.07/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.07/2.51  git: non_committed_changes: false
% 15.07/2.51  git: last_make_outside_of_git: false
% 15.07/2.51  
% 15.07/2.51  ------ 
% 15.07/2.51  ------ Parsing...
% 15.07/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.07/2.51  
% 15.07/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 15.07/2.51  
% 15.07/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.07/2.51  
% 15.07/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.07/2.51  ------ Proving...
% 15.07/2.51  ------ Problem Properties 
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  clauses                                 30
% 15.07/2.51  conjectures                             1
% 15.07/2.51  EPR                                     0
% 15.07/2.51  Horn                                    23
% 15.07/2.51  unary                                   6
% 15.07/2.51  binary                                  3
% 15.07/2.51  lits                                    87
% 15.07/2.51  lits eq                                 22
% 15.07/2.51  fd_pure                                 0
% 15.07/2.51  fd_pseudo                               0
% 15.07/2.51  fd_cond                                 3
% 15.07/2.51  fd_pseudo_cond                          3
% 15.07/2.51  AC symbols                              0
% 15.07/2.51  
% 15.07/2.51  ------ Input Options Time Limit: Unbounded
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  ------ 
% 15.07/2.51  Current options:
% 15.07/2.51  ------ 
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  ------ Proving...
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  % SZS status Theorem for theBenchmark.p
% 15.07/2.51  
% 15.07/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.07/2.51  
% 15.07/2.51  fof(f8,axiom,(
% 15.07/2.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f28,plain,(
% 15.07/2.51    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f8])).
% 15.07/2.51  
% 15.07/2.51  fof(f29,plain,(
% 15.07/2.51    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f28])).
% 15.07/2.51  
% 15.07/2.51  fof(f47,plain,(
% 15.07/2.51    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f29])).
% 15.07/2.51  
% 15.07/2.51  fof(f48,plain,(
% 15.07/2.51    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(rectify,[],[f47])).
% 15.07/2.51  
% 15.07/2.51  fof(f50,plain,(
% 15.07/2.51    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f49,plain,(
% 15.07/2.51    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f51,plain,(
% 15.07/2.51    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 15.07/2.51  
% 15.07/2.51  fof(f93,plain,(
% 15.07/2.51    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f51])).
% 15.07/2.51  
% 15.07/2.51  fof(f13,conjecture,(
% 15.07/2.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f14,negated_conjecture,(
% 15.07/2.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 15.07/2.51    inference(negated_conjecture,[],[f13])).
% 15.07/2.51  
% 15.07/2.51  fof(f38,plain,(
% 15.07/2.51    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f14])).
% 15.07/2.51  
% 15.07/2.51  fof(f39,plain,(
% 15.07/2.51    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f38])).
% 15.07/2.51  
% 15.07/2.51  fof(f72,plain,(
% 15.07/2.51    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) | ~l3_lattices(sK10) | ~v13_lattices(sK10) | ~v10_lattices(sK10) | v2_struct_0(sK10)) & l3_lattices(sK10) & v4_lattice3(sK10) & v10_lattices(sK10) & ~v2_struct_0(sK10))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f73,plain,(
% 15.07/2.51    (k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) | ~l3_lattices(sK10) | ~v13_lattices(sK10) | ~v10_lattices(sK10) | v2_struct_0(sK10)) & l3_lattices(sK10) & v4_lattice3(sK10) & v10_lattices(sK10) & ~v2_struct_0(sK10)),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f39,f72])).
% 15.07/2.51  
% 15.07/2.51  fof(f114,plain,(
% 15.07/2.51    ~v2_struct_0(sK10)),
% 15.07/2.51    inference(cnf_transformation,[],[f73])).
% 15.07/2.51  
% 15.07/2.51  fof(f117,plain,(
% 15.07/2.51    l3_lattices(sK10)),
% 15.07/2.51    inference(cnf_transformation,[],[f73])).
% 15.07/2.51  
% 15.07/2.51  fof(f6,axiom,(
% 15.07/2.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f15,plain,(
% 15.07/2.51    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 15.07/2.51    inference(pure_predicate_removal,[],[f6])).
% 15.07/2.51  
% 15.07/2.51  fof(f25,plain,(
% 15.07/2.51    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 15.07/2.51    inference(ennf_transformation,[],[f15])).
% 15.07/2.51  
% 15.07/2.51  fof(f87,plain,(
% 15.07/2.51    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f25])).
% 15.07/2.51  
% 15.07/2.51  fof(f5,axiom,(
% 15.07/2.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f23,plain,(
% 15.07/2.51    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f5])).
% 15.07/2.51  
% 15.07/2.51  fof(f24,plain,(
% 15.07/2.51    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f23])).
% 15.07/2.51  
% 15.07/2.51  fof(f86,plain,(
% 15.07/2.51    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f24])).
% 15.07/2.51  
% 15.07/2.51  fof(f12,axiom,(
% 15.07/2.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f36,plain,(
% 15.07/2.51    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f12])).
% 15.07/2.51  
% 15.07/2.51  fof(f37,plain,(
% 15.07/2.51    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f36])).
% 15.07/2.51  
% 15.07/2.51  fof(f67,plain,(
% 15.07/2.51    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f37])).
% 15.07/2.51  
% 15.07/2.51  fof(f68,plain,(
% 15.07/2.51    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(rectify,[],[f67])).
% 15.07/2.51  
% 15.07/2.51  fof(f70,plain,(
% 15.07/2.51    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK9(X0)) != k2_lattices(X0,sK9(X0),X1) & m1_subset_1(sK9(X0),u1_struct_0(X0))))) )),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f69,plain,(
% 15.07/2.51    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK8(X0)) != k2_lattices(X0,sK8(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f71,plain,(
% 15.07/2.51    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK8(X0),sK9(X0)) != k2_lattices(X0,sK9(X0),sK8(X0)) & m1_subset_1(sK9(X0),u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f68,f70,f69])).
% 15.07/2.51  
% 15.07/2.51  fof(f110,plain,(
% 15.07/2.51    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f71])).
% 15.07/2.51  
% 15.07/2.51  fof(f3,axiom,(
% 15.07/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f16,plain,(
% 15.07/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.07/2.51    inference(pure_predicate_removal,[],[f3])).
% 15.07/2.51  
% 15.07/2.51  fof(f17,plain,(
% 15.07/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 15.07/2.51    inference(pure_predicate_removal,[],[f16])).
% 15.07/2.51  
% 15.07/2.51  fof(f18,plain,(
% 15.07/2.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 15.07/2.51    inference(pure_predicate_removal,[],[f17])).
% 15.07/2.51  
% 15.07/2.51  fof(f19,plain,(
% 15.07/2.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 15.07/2.51    inference(ennf_transformation,[],[f18])).
% 15.07/2.51  
% 15.07/2.51  fof(f20,plain,(
% 15.07/2.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 15.07/2.51    inference(flattening,[],[f19])).
% 15.07/2.51  
% 15.07/2.51  fof(f79,plain,(
% 15.07/2.51    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f20])).
% 15.07/2.51  
% 15.07/2.51  fof(f115,plain,(
% 15.07/2.51    v10_lattices(sK10)),
% 15.07/2.51    inference(cnf_transformation,[],[f73])).
% 15.07/2.51  
% 15.07/2.51  fof(f10,axiom,(
% 15.07/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f32,plain,(
% 15.07/2.51    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f10])).
% 15.07/2.51  
% 15.07/2.51  fof(f33,plain,(
% 15.07/2.51    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f32])).
% 15.07/2.51  
% 15.07/2.51  fof(f56,plain,(
% 15.07/2.51    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f33])).
% 15.07/2.51  
% 15.07/2.51  fof(f57,plain,(
% 15.07/2.51    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(rectify,[],[f56])).
% 15.07/2.51  
% 15.07/2.51  fof(f60,plain,(
% 15.07/2.51    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK6(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK6(X0,X4),X4) & m1_subset_1(sK6(X0,X4),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f59,plain,(
% 15.07/2.51    ( ! [X1] : (! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK5(X0,X2)) & r4_lattice3(X0,sK5(X0,X2),X1) & m1_subset_1(sK5(X0,X2),u1_struct_0(X0))))) )),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f58,plain,(
% 15.07/2.51    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK4(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK4(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f61,plain,(
% 15.07/2.51    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK5(X0,X2)) & r4_lattice3(X0,sK5(X0,X2),sK4(X0)) & m1_subset_1(sK5(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK4(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK6(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK6(X0,X4),X4) & m1_subset_1(sK6(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f57,f60,f59,f58])).
% 15.07/2.51  
% 15.07/2.51  fof(f99,plain,(
% 15.07/2.51    ( ! [X4,X0] : (m1_subset_1(sK6(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f61])).
% 15.07/2.51  
% 15.07/2.51  fof(f116,plain,(
% 15.07/2.51    v4_lattice3(sK10)),
% 15.07/2.51    inference(cnf_transformation,[],[f73])).
% 15.07/2.51  
% 15.07/2.51  fof(f81,plain,(
% 15.07/2.51    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f20])).
% 15.07/2.51  
% 15.07/2.51  fof(f7,axiom,(
% 15.07/2.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f26,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f7])).
% 15.07/2.51  
% 15.07/2.51  fof(f27,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f26])).
% 15.07/2.51  
% 15.07/2.51  fof(f46,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f27])).
% 15.07/2.51  
% 15.07/2.51  fof(f88,plain,(
% 15.07/2.51    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f46])).
% 15.07/2.51  
% 15.07/2.51  fof(f80,plain,(
% 15.07/2.51    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f20])).
% 15.07/2.51  
% 15.07/2.51  fof(f94,plain,(
% 15.07/2.51    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f51])).
% 15.07/2.51  
% 15.07/2.51  fof(f101,plain,(
% 15.07/2.51    ( ! [X6,X4,X0] : (r1_lattices(X0,sK6(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f61])).
% 15.07/2.51  
% 15.07/2.51  fof(f1,axiom,(
% 15.07/2.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f40,plain,(
% 15.07/2.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.07/2.51    inference(nnf_transformation,[],[f1])).
% 15.07/2.51  
% 15.07/2.51  fof(f41,plain,(
% 15.07/2.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.07/2.51    inference(flattening,[],[f40])).
% 15.07/2.51  
% 15.07/2.51  fof(f76,plain,(
% 15.07/2.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 15.07/2.51    inference(cnf_transformation,[],[f41])).
% 15.07/2.51  
% 15.07/2.51  fof(f119,plain,(
% 15.07/2.51    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.07/2.51    inference(equality_resolution,[],[f76])).
% 15.07/2.51  
% 15.07/2.51  fof(f2,axiom,(
% 15.07/2.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f77,plain,(
% 15.07/2.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 15.07/2.51    inference(cnf_transformation,[],[f2])).
% 15.07/2.51  
% 15.07/2.51  fof(f9,axiom,(
% 15.07/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f30,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f9])).
% 15.07/2.51  
% 15.07/2.51  fof(f31,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f30])).
% 15.07/2.51  
% 15.07/2.51  fof(f52,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f31])).
% 15.07/2.51  
% 15.07/2.51  fof(f53,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(rectify,[],[f52])).
% 15.07/2.51  
% 15.07/2.51  fof(f54,plain,(
% 15.07/2.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f55,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 15.07/2.51  
% 15.07/2.51  fof(f97,plain,(
% 15.07/2.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f55])).
% 15.07/2.51  
% 15.07/2.51  fof(f90,plain,(
% 15.07/2.51    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f51])).
% 15.07/2.51  
% 15.07/2.51  fof(f92,plain,(
% 15.07/2.51    ( ! [X4,X0] : (k2_lattices(X0,X4,sK2(X0)) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f51])).
% 15.07/2.51  
% 15.07/2.51  fof(f4,axiom,(
% 15.07/2.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f21,plain,(
% 15.07/2.51    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f4])).
% 15.07/2.51  
% 15.07/2.51  fof(f22,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f21])).
% 15.07/2.51  
% 15.07/2.51  fof(f42,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f22])).
% 15.07/2.51  
% 15.07/2.51  fof(f43,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(rectify,[],[f42])).
% 15.07/2.51  
% 15.07/2.51  fof(f44,plain,(
% 15.07/2.51    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f45,plain,(
% 15.07/2.51    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 15.07/2.51  
% 15.07/2.51  fof(f82,plain,(
% 15.07/2.51    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f45])).
% 15.07/2.51  
% 15.07/2.51  fof(f122,plain,(
% 15.07/2.51    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(equality_resolution,[],[f82])).
% 15.07/2.51  
% 15.07/2.51  fof(f11,axiom,(
% 15.07/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 15.07/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.51  
% 15.07/2.51  fof(f34,plain,(
% 15.07/2.51    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.07/2.51    inference(ennf_transformation,[],[f11])).
% 15.07/2.51  
% 15.07/2.51  fof(f35,plain,(
% 15.07/2.51    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f34])).
% 15.07/2.51  
% 15.07/2.51  fof(f62,plain,(
% 15.07/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(nnf_transformation,[],[f35])).
% 15.07/2.51  
% 15.07/2.51  fof(f63,plain,(
% 15.07/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(flattening,[],[f62])).
% 15.07/2.51  
% 15.07/2.51  fof(f64,plain,(
% 15.07/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(rectify,[],[f63])).
% 15.07/2.51  
% 15.07/2.51  fof(f65,plain,(
% 15.07/2.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK7(X0,X1,X2)) & r4_lattice3(X0,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 15.07/2.51    introduced(choice_axiom,[])).
% 15.07/2.51  
% 15.07/2.51  fof(f66,plain,(
% 15.07/2.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK7(X0,X1,X2)) & r4_lattice3(X0,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.07/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f64,f65])).
% 15.07/2.51  
% 15.07/2.51  fof(f108,plain,(
% 15.07/2.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK7(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f66])).
% 15.07/2.51  
% 15.07/2.51  fof(f109,plain,(
% 15.07/2.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK7(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f66])).
% 15.07/2.51  
% 15.07/2.51  fof(f107,plain,(
% 15.07/2.51    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f66])).
% 15.07/2.51  
% 15.07/2.51  fof(f100,plain,(
% 15.07/2.51    ( ! [X4,X0] : (r4_lattice3(X0,sK6(X0,X4),X4) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.07/2.51    inference(cnf_transformation,[],[f61])).
% 15.07/2.51  
% 15.07/2.51  fof(f118,plain,(
% 15.07/2.51    k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) | ~l3_lattices(sK10) | ~v13_lattices(sK10) | ~v10_lattices(sK10) | v2_struct_0(sK10)),
% 15.07/2.51    inference(cnf_transformation,[],[f73])).
% 15.07/2.51  
% 15.07/2.51  cnf(c_17,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | v13_lattices(X1)
% 15.07/2.51      | v2_struct_0(X1) ),
% 15.07/2.51      inference(cnf_transformation,[],[f93]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_44,negated_conjecture,
% 15.07/2.51      ( ~ v2_struct_0(sK10) ),
% 15.07/2.51      inference(cnf_transformation,[],[f114]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1376,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | v13_lattices(X1)
% 15.07/2.51      | sK10 != X1 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_17,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1377,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1376]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_41,negated_conjecture,
% 15.07/2.51      ( l3_lattices(sK10) ),
% 15.07/2.51      inference(cnf_transformation,[],[f117]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_13,plain,
% 15.07/2.51      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f87]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_123,plain,
% 15.07/2.51      ( l1_lattices(sK10) | ~ l3_lattices(sK10) ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_13]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1381,plain,
% 15.07/2.51      ( m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1377,c_41,c_123]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1382,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_1381]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3554,plain,
% 15.07/2.51      ( m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10)) = iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_12,plain,
% 15.07/2.51      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 15.07/2.51      | ~ l1_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f86]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1305,plain,
% 15.07/2.51      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 15.07/2.51      | ~ l1_lattices(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_12,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1306,plain,
% 15.07/2.51      ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1305]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_126,plain,
% 15.07/2.51      ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10) ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_12]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1308,plain,
% 15.07/2.51      ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10)) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1306,c_44,c_41,c_123,c_126]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3557,plain,
% 15.07/2.51      ( m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10)) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1308]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_39,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | ~ v6_lattices(X1)
% 15.07/2.51      | v2_struct_0(X1)
% 15.07/2.51      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 15.07/2.51      inference(cnf_transformation,[],[f110]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1316,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | ~ v6_lattices(X1)
% 15.07/2.51      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 15.07/2.51      | sK10 != X1 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_39,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1317,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | ~ v6_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X1,X0) = k2_lattices(sK10,X0,X1) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1316]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_6,plain,
% 15.07/2.51      ( v6_lattices(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f79]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_43,negated_conjecture,
% 15.07/2.51      ( v10_lattices(sK10) ),
% 15.07/2.51      inference(cnf_transformation,[],[f115]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_904,plain,
% 15.07/2.51      ( v6_lattices(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_6,c_43]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_905,plain,
% 15.07/2.51      ( v6_lattices(sK10) | ~ l3_lattices(sK10) | v2_struct_0(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_904]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_142,plain,
% 15.07/2.51      ( v6_lattices(sK10)
% 15.07/2.51      | ~ l3_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | ~ v10_lattices(sK10) ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_6]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_907,plain,
% 15.07/2.51      ( v6_lattices(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_905,c_44,c_43,c_41,c_142]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1016,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | v2_struct_0(X1)
% 15.07/2.51      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 15.07/2.51      | sK10 != X1 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_39,c_907]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1017,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | k2_lattices(sK10,X1,X0) = k2_lattices(sK10,X0,X1) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1016]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1320,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | k2_lattices(sK10,X1,X0) = k2_lattices(sK10,X0,X1) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1317,c_44,c_41,c_123,c_1017]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1321,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | k2_lattices(sK10,X0,X1) = k2_lattices(sK10,X1,X0) ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_1320]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3566,plain,
% 15.07/2.51      ( k2_lattices(sK10,X0,X1) = k2_lattices(sK10,X1,X0)
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5159,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK1(sK10,X0),X1) = k2_lattices(sK10,X1,sK1(sK10,X0))
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3554,c_3566]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_20821,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK1(sK10,X0),sK1(sK10,X1)) = k2_lattices(sK10,sK1(sK10,X1),sK1(sK10,X0))
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3554,c_5159]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_37767,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK1(sK10,k5_lattices(sK10)),sK1(sK10,X0)) = k2_lattices(sK10,sK1(sK10,X0),sK1(sK10,k5_lattices(sK10)))
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3557,c_20821]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_37839,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK1(sK10,sK1(sK10,X0)),sK1(sK10,k5_lattices(sK10))) = k2_lattices(sK10,sK1(sK10,k5_lattices(sK10)),sK1(sK10,sK1(sK10,X0)))
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3554,c_37767]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_38793,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK1(sK10,k5_lattices(sK10)),sK1(sK10,sK1(sK10,sK1(sK10,X0)))) = k2_lattices(sK10,sK1(sK10,sK1(sK10,sK1(sK10,X0))),sK1(sK10,k5_lattices(sK10)))
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3554,c_37839]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_30,plain,
% 15.07/2.51      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f99]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1058,plain,
% 15.07/2.51      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1059,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | ~ v4_lattice3(sK10)
% 15.07/2.51      | v2_struct_0(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1058]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_42,negated_conjecture,
% 15.07/2.51      ( v4_lattice3(sK10) ),
% 15.07/2.51      inference(cnf_transformation,[],[f116]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1063,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1059,c_44,c_42]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_31038,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10)) ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_1063]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_31039,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10)) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_31038]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3033,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3032,plain,( X0 = X0 ),theory(equality) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5667,plain,
% 15.07/2.51      ( X0 != X1 | X1 = X0 ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_3033,c_3032]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4,plain,
% 15.07/2.51      ( ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | v9_lattices(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f81]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_15,plain,
% 15.07/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.07/2.51      | ~ v8_lattices(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v9_lattices(X0)
% 15.07/2.51      | k2_lattices(X0,X1,X2) = X1 ),
% 15.07/2.51      inference(cnf_transformation,[],[f88]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_537,plain,
% 15.07/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.07/2.51      | ~ v8_lattices(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | k2_lattices(X0,X1,X2) = X1 ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_4,c_15]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5,plain,
% 15.07/2.51      ( v8_lattices(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f80]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_541,plain,
% 15.07/2.51      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ r1_lattices(X0,X1,X2)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | k2_lattices(X0,X1,X2) = X1 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_537,c_5]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_542,plain,
% 15.07/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | k2_lattices(X0,X1,X2) = X1 ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_541]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_766,plain,
% 15.07/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | k2_lattices(X0,X1,X2) = X1
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_542,c_43]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_767,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ l3_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,X1) = X0 ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_766]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_771,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | k2_lattices(sK10,X0,X1) = X0 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_767,c_44,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_8301,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | X0 = k2_lattices(sK10,X0,X1) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_5667,c_771]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5674,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | X2 != k2_lattices(sK10,X0,X1)
% 15.07/2.51      | k2_lattices(sK10,X1,X0) = X2 ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_3033,c_1321]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_8547,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | k2_lattices(sK10,X1,X0) = X0 ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_8301,c_5674]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_16,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | v13_lattices(X1)
% 15.07/2.51      | v2_struct_0(X1)
% 15.07/2.51      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 15.07/2.51      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 15.07/2.51      inference(cnf_transformation,[],[f94]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1397,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | v13_lattices(X1)
% 15.07/2.51      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 15.07/2.51      | k2_lattices(X1,sK1(X1,X0),X0) != X0
% 15.07/2.51      | sK10 != X1 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_16,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1398,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0
% 15.07/2.51      | k2_lattices(sK10,sK1(sK10,X0),X0) != X0 ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1397]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1402,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0
% 15.07/2.51      | k2_lattices(sK10,sK1(sK10,X0),X0) != X0 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1398,c_41,c_123]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54032,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0 ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_8547,c_1402]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54181,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ r1_lattices(sK10,X0,sK1(sK10,X0))
% 15.07/2.51      | v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_54032,c_1382]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54182,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK1(sK10,X0)) != X0 ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_54181]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54506,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(sK1(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_54182,c_771]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54523,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ r1_lattices(sK10,X0,sK1(sK10,X0))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_54506,c_41,c_123,c_1377]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54524,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,sK1(sK10,X0))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_54523]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_28,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | r1_lattices(X0,sK6(X0,X2),X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f101]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1088,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | r1_lattices(X0,sK6(X0,X2),X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1089,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | r1_lattices(sK10,sK6(sK10,X1),X0)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ v4_lattice3(sK10)
% 15.07/2.51      | v2_struct_0(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1088]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1093,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | r1_lattices(sK10,sK6(sK10,X1),X0)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1089,c_44,c_42]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_54549,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK1(sK10,sK6(sK10,X0)),X0)
% 15.07/2.51      | ~ m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(sK1(sK10,sK6(sK10,X0)),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_54524,c_1093]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3826,plain,
% 15.07/2.51      ( ~ m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | m1_subset_1(sK1(sK10,sK6(sK10,X0)),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_1382]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_55176,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK1(sK10,sK6(sK10,X0)),X0)
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_54549,c_44,c_42,c_1059,c_3826]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3035,plain,
% 15.07/2.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.07/2.51      theory(equality) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_0,plain,
% 15.07/2.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.07/2.51      inference(cnf_transformation,[],[f119]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5769,plain,
% 15.07/2.51      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 15.07/2.51      | ~ r2_hidden(X2,k1_xboole_0)
% 15.07/2.51      | X0 != X2 ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_3035,c_0]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_9756,plain,
% 15.07/2.51      ( ~ r1_lattices(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ r2_hidden(X0,k1_xboole_0)
% 15.07/2.51      | r2_hidden(k2_lattices(sK10,X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_5769,c_771]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3,plain,
% 15.07/2.51      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 15.07/2.51      inference(cnf_transformation,[],[f77]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3575,plain,
% 15.07/2.51      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4884,plain,
% 15.07/2.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_0,c_3575]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4890,plain,
% 15.07/2.51      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 15.07/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_4884]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10374,plain,
% 15.07/2.51      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_9756,c_4890]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_22,plain,
% 15.07/2.51      ( r4_lattice3(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | r2_hidden(sK3(X0,X1,X2),X2)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f97]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1163,plain,
% 15.07/2.51      ( r4_lattice3(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | r2_hidden(sK3(X0,X1,X2),X2)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_22,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1164,plain,
% 15.07/2.51      ( r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | r2_hidden(sK3(sK10,X0,X1),X1)
% 15.07/2.51      | v2_struct_0(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1163]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1168,plain,
% 15.07/2.51      ( r2_hidden(sK3(sK10,X0,X1),X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | r4_lattice3(sK10,X0,X1) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1164,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1169,plain,
% 15.07/2.51      ( r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | r2_hidden(sK3(sK10,X0,X1),X1) ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_1168]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10484,plain,
% 15.07/2.51      ( r4_lattice3(sK10,X0,k1_xboole_0)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_10374,c_1169]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_56902,plain,
% 15.07/2.51      ( ~ m1_subset_1(sK1(sK10,sK6(sK10,k1_xboole_0)),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_55176,c_10484]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_58627,plain,
% 15.07/2.51      ( ~ m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10))
% 15.07/2.51      | v13_lattices(sK10) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_56902,c_1382]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_58628,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,k1_xboole_0),u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_58627]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59462,plain,
% 15.07/2.51      ( v13_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_38793,c_31039,c_58628]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_20,plain,
% 15.07/2.51      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 15.07/2.51      | ~ l1_lattices(X0)
% 15.07/2.51      | ~ v13_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f90]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1291,plain,
% 15.07/2.51      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 15.07/2.51      | ~ l1_lattices(X0)
% 15.07/2.51      | ~ v13_lattices(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_20,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1292,plain,
% 15.07/2.51      ( m1_subset_1(sK2(sK10),u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | ~ v13_lattices(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1291]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1294,plain,
% 15.07/2.51      ( m1_subset_1(sK2(sK10),u1_struct_0(sK10)) | ~ v13_lattices(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1292,c_41,c_123]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3558,plain,
% 15.07/2.51      ( m1_subset_1(sK2(sK10),u1_struct_0(sK10)) = iProver_top
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3560,plain,
% 15.07/2.51      ( r4_lattice3(sK10,X0,X1) = iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | r2_hidden(sK3(sK10,X0,X1),X1) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1169]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5195,plain,
% 15.07/2.51      ( r4_lattice3(sK10,X0,k1_xboole_0) = iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3560,c_4884]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5595,plain,
% 15.07/2.51      ( r4_lattice3(sK10,sK2(sK10),k1_xboole_0) = iProver_top
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3558,c_5195]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3563,plain,
% 15.07/2.51      ( r4_lattice3(sK10,X0,X1) != iProver_top
% 15.07/2.51      | r1_lattices(sK10,sK6(sK10,X1),X0) = iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3572,plain,
% 15.07/2.51      ( k2_lattices(sK10,X0,X1) = X0
% 15.07/2.51      | r1_lattices(sK10,X0,X1) != iProver_top
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4559,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0)
% 15.07/2.51      | r4_lattice3(sK10,X1,X0) != iProver_top
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3563,c_3572]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_45,plain,
% 15.07/2.51      ( v2_struct_0(sK10) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_47,plain,
% 15.07/2.51      ( v4_lattice3(sK10) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1060,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) = iProver_top
% 15.07/2.51      | v4_lattice3(sK10) != iProver_top
% 15.07/2.51      | v2_struct_0(sK10) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1059]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1602,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X3,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | X0 != X2
% 15.07/2.51      | k2_lattices(sK10,X3,X2) = X3
% 15.07/2.51      | sK6(sK10,X1) != X3
% 15.07/2.51      | sK10 != sK10 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_771,c_1093]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1603,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10))
% 15.07/2.51      | k2_lattices(sK10,sK6(sK10,X1),X0) = sK6(sK10,X1) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1602]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1604,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0)
% 15.07/2.51      | r4_lattice3(sK10,X1,X0) != iProver_top
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1603]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_7822,plain,
% 15.07/2.51      ( m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | r4_lattice3(sK10,X1,X0) != iProver_top
% 15.07/2.51      | k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_4559,c_45,c_47,c_1060,c_1604]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_7823,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,X0),X1) = sK6(sK10,X0)
% 15.07/2.51      | r4_lattice3(sK10,X1,X0) != iProver_top
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_7822]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_7831,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),sK2(sK10)) = sK6(sK10,k1_xboole_0)
% 15.07/2.51      | m1_subset_1(sK2(sK10),u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_5595,c_7823]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_48,plain,
% 15.07/2.51      ( l3_lattices(sK10) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_101,plain,
% 15.07/2.51      ( m1_subset_1(sK2(X0),u1_struct_0(X0)) = iProver_top
% 15.07/2.51      | l1_lattices(X0) != iProver_top
% 15.07/2.51      | v13_lattices(X0) != iProver_top
% 15.07/2.51      | v2_struct_0(X0) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_103,plain,
% 15.07/2.51      ( m1_subset_1(sK2(sK10),u1_struct_0(sK10)) = iProver_top
% 15.07/2.51      | l1_lattices(sK10) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) != iProver_top
% 15.07/2.51      | v2_struct_0(sK10) = iProver_top ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_101]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_122,plain,
% 15.07/2.51      ( l1_lattices(X0) = iProver_top | l3_lattices(X0) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_124,plain,
% 15.07/2.51      ( l1_lattices(sK10) = iProver_top
% 15.07/2.51      | l3_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(instantiation,[status(thm)],[c_122]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_8031,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),sK2(sK10)) = sK6(sK10,k1_xboole_0)
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_7831,c_45,c_48,c_103,c_124]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59503,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),sK2(sK10)) = sK6(sK10,k1_xboole_0) ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_59462,c_8031]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_18,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | ~ v13_lattices(X1)
% 15.07/2.51      | v2_struct_0(X1)
% 15.07/2.51      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
% 15.07/2.51      inference(cnf_transformation,[],[f92]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1355,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | ~ v13_lattices(X1)
% 15.07/2.51      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
% 15.07/2.51      | sK10 != X1 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_18,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1356,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | ~ v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK2(sK10)) = sK2(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1355]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1360,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,X0,sK2(sK10)) = sK2(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1356,c_41,c_123]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3555,plain,
% 15.07/2.51      ( k2_lattices(sK10,X0,sK2(sK10)) = sK2(sK10)
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4339,plain,
% 15.07/2.51      ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = sK2(sK10)
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3557,c_3555]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59510,plain,
% 15.07/2.51      ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = sK2(sK10) ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_59462,c_4339]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_11,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | ~ v13_lattices(X1)
% 15.07/2.51      | v2_struct_0(X1)
% 15.07/2.51      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 15.07/2.51      inference(cnf_transformation,[],[f122]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1421,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.07/2.51      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 15.07/2.51      | ~ l1_lattices(X1)
% 15.07/2.51      | ~ v13_lattices(X1)
% 15.07/2.51      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 15.07/2.51      | sK10 != X1 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_11,c_44]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1422,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(k5_lattices(sK10),u1_struct_0(sK10))
% 15.07/2.51      | ~ l1_lattices(sK10)
% 15.07/2.51      | ~ v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,k5_lattices(sK10),X0) = k5_lattices(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1421]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1426,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ v13_lattices(sK10)
% 15.07/2.51      | k2_lattices(sK10,k5_lattices(sK10),X0) = k5_lattices(sK10) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1422,c_44,c_41,c_123,c_126]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3552,plain,
% 15.07/2.51      ( k2_lattices(sK10,k5_lattices(sK10),X0) = k5_lattices(sK10)
% 15.07/2.51      | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1426]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3993,plain,
% 15.07/2.51      ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = k5_lattices(sK10)
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3558,c_3552]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59512,plain,
% 15.07/2.51      ( k2_lattices(sK10,k5_lattices(sK10),sK2(sK10)) = k5_lattices(sK10) ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_59462,c_3993]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59523,plain,
% 15.07/2.51      ( sK2(sK10) = k5_lattices(sK10) ),
% 15.07/2.51      inference(light_normalisation,[status(thm)],[c_59510,c_59512]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59538,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,k1_xboole_0),k5_lattices(sK10)) = sK6(sK10,k1_xboole_0) ),
% 15.07/2.51      inference(light_normalisation,[status(thm)],[c_59503,c_59523]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3565,plain,
% 15.07/2.51      ( m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) = iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4340,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,X0),sK2(sK10)) = sK2(sK10)
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3565,c_3555]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59507,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,X0),sK2(sK10)) = sK2(sK10) ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_59462,c_4340]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59532,plain,
% 15.07/2.51      ( k2_lattices(sK10,sK6(sK10,X0),k5_lattices(sK10)) = k5_lattices(sK10) ),
% 15.07/2.51      inference(light_normalisation,[status(thm)],[c_59507,c_59523]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_59539,plain,
% 15.07/2.51      ( sK6(sK10,k1_xboole_0) = k5_lattices(sK10) ),
% 15.07/2.51      inference(demodulation,[status(thm)],[c_59538,c_59532]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_32,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | r4_lattice3(X0,sK7(X0,X2,X1),X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | k15_lattice3(X0,X2) = X1 ),
% 15.07/2.51      inference(cnf_transformation,[],[f108]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_856,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | r4_lattice3(X0,sK7(X0,X2,X1),X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | k15_lattice3(X0,X2) = X1
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_32,c_43]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_857,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X1,X0),X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ v4_lattice3(sK10)
% 15.07/2.51      | ~ l3_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_856]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_861,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X1,X0),X1)
% 15.07/2.51      | ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_857,c_44,c_42,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_862,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X1,X0),X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_861]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3568,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = X1
% 15.07/2.51      | r4_lattice3(sK10,X1,X0) != iProver_top
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X0,X1),X0) = iProver_top
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_31,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | ~ r1_lattices(X0,X1,sK7(X0,X2,X1))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | k15_lattice3(X0,X2) = X1 ),
% 15.07/2.51      inference(cnf_transformation,[],[f109]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_880,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | ~ r1_lattices(X0,X1,sK7(X0,X2,X1))
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | k15_lattice3(X0,X2) = X1
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_31,c_43]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_881,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ r1_lattices(sK10,X0,sK7(sK10,X1,X0))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ v4_lattice3(sK10)
% 15.07/2.51      | ~ l3_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_880]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_885,plain,
% 15.07/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ r1_lattices(sK10,X0,sK7(sK10,X1,X0))
% 15.07/2.51      | ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_881,c_44,c_42,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_886,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ r1_lattices(sK10,X0,sK7(sK10,X1,X0))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_885]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3567,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = X1
% 15.07/2.51      | r4_lattice3(sK10,X1,X0) != iProver_top
% 15.07/2.51      | r1_lattices(sK10,X1,sK7(sK10,X0,X1)) != iProver_top
% 15.07/2.51      | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4967,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = sK6(sK10,X1)
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1) != iProver_top
% 15.07/2.51      | r4_lattice3(sK10,sK6(sK10,X1),X0) != iProver_top
% 15.07/2.51      | m1_subset_1(sK7(sK10,X0,sK6(sK10,X1)),u1_struct_0(sK10)) != iProver_top
% 15.07/2.51      | m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3563,c_3567]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1706,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ r4_lattice3(sK10,X2,X3)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK10))
% 15.07/2.51      | sK7(sK10,X1,X0) != X2
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0
% 15.07/2.51      | sK6(sK10,X3) != X0
% 15.07/2.51      | sK10 != sK10 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_886,c_1093]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1707,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
% 15.07/2.51      | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
% 15.07/2.51      | ~ m1_subset_1(sK7(sK10,X0,sK6(sK10,X1)),u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10))
% 15.07/2.51      | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1706]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_33,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | m1_subset_1(sK7(X0,X2,X1),u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | ~ v10_lattices(X0)
% 15.07/2.51      | k15_lattice3(X0,X2) = X1 ),
% 15.07/2.51      inference(cnf_transformation,[],[f107]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_832,plain,
% 15.07/2.51      ( ~ r4_lattice3(X0,X1,X2)
% 15.07/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.07/2.51      | m1_subset_1(sK7(X0,X2,X1),u1_struct_0(X0))
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | k15_lattice3(X0,X2) = X1
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_33,c_43]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_833,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | m1_subset_1(sK7(sK10,X1,X0),u1_struct_0(sK10))
% 15.07/2.51      | ~ v4_lattice3(sK10)
% 15.07/2.51      | ~ l3_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_832]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_837,plain,
% 15.07/2.51      ( m1_subset_1(sK7(sK10,X1,X0),u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_833,c_44,c_42,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_838,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,X0,X1)
% 15.07/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK10))
% 15.07/2.51      | m1_subset_1(sK7(sK10,X1,X0),u1_struct_0(sK10))
% 15.07/2.51      | k15_lattice3(sK10,X1) = X0 ),
% 15.07/2.51      inference(renaming,[status(thm)],[c_837]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1721,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
% 15.07/2.51      | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
% 15.07/2.51      | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
% 15.07/2.51      inference(forward_subsumption_resolution,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_1707,c_1063,c_838]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1725,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = sK6(sK10,X1)
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1) != iProver_top
% 15.07/2.51      | r4_lattice3(sK10,sK6(sK10,X1),X0) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10047,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = sK6(sK10,X1)
% 15.07/2.51      | r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1) != iProver_top
% 15.07/2.51      | r4_lattice3(sK10,sK6(sK10,X1),X0) != iProver_top ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_4967,c_1725]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10054,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = sK6(sK10,X0)
% 15.07/2.51      | r4_lattice3(sK10,sK6(sK10,X0),X0) != iProver_top
% 15.07/2.51      | m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10)) != iProver_top ),
% 15.07/2.51      inference(superposition,[status(thm)],[c_3568,c_10047]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_29,plain,
% 15.07/2.51      ( r4_lattice3(X0,sK6(X0,X1),X1)
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | ~ l3_lattices(X0)
% 15.07/2.51      | v2_struct_0(X0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f100]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1073,plain,
% 15.07/2.51      ( r4_lattice3(X0,sK6(X0,X1),X1)
% 15.07/2.51      | ~ v4_lattice3(X0)
% 15.07/2.51      | v2_struct_0(X0)
% 15.07/2.51      | sK10 != X0 ),
% 15.07/2.51      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_1074,plain,
% 15.07/2.51      ( r4_lattice3(sK10,sK6(sK10,X0),X0)
% 15.07/2.51      | ~ v4_lattice3(sK10)
% 15.07/2.51      | v2_struct_0(sK10) ),
% 15.07/2.51      inference(unflattening,[status(thm)],[c_1073]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_4591,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
% 15.07/2.51      | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
% 15.07/2.51      | ~ m1_subset_1(sK7(sK10,X0,sK6(sK10,X1)),u1_struct_0(sK10))
% 15.07/2.51      | ~ m1_subset_1(sK6(sK10,X1),u1_struct_0(sK10))
% 15.07/2.51      | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_886,c_1093]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5130,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK7(sK10,X0,sK6(sK10,X1)),X1)
% 15.07/2.51      | ~ r4_lattice3(sK10,sK6(sK10,X1),X0)
% 15.07/2.51      | k15_lattice3(sK10,X0) = sK6(sK10,X1) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_4591,c_1721]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_5207,plain,
% 15.07/2.51      ( ~ r4_lattice3(sK10,sK6(sK10,X0),X0)
% 15.07/2.51      | ~ m1_subset_1(sK6(sK10,X0),u1_struct_0(sK10))
% 15.07/2.51      | k15_lattice3(sK10,X0) = sK6(sK10,X0) ),
% 15.07/2.51      inference(resolution,[status(thm)],[c_5130,c_862]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10274,plain,
% 15.07/2.51      ( k15_lattice3(sK10,X0) = sK6(sK10,X0) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_10054,c_44,c_42,c_1059,c_1074,c_5207]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_40,negated_conjecture,
% 15.07/2.51      ( ~ v13_lattices(sK10)
% 15.07/2.51      | ~ l3_lattices(sK10)
% 15.07/2.51      | v2_struct_0(sK10)
% 15.07/2.51      | ~ v10_lattices(sK10)
% 15.07/2.51      | k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) ),
% 15.07/2.51      inference(cnf_transformation,[],[f118]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_245,negated_conjecture,
% 15.07/2.51      ( ~ v13_lattices(sK10)
% 15.07/2.51      | k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0) ),
% 15.07/2.51      inference(global_propositional_subsumption,
% 15.07/2.51                [status(thm)],
% 15.07/2.51                [c_40,c_44,c_43,c_41]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_3574,plain,
% 15.07/2.51      ( k5_lattices(sK10) != k15_lattice3(sK10,k1_xboole_0)
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10277,plain,
% 15.07/2.51      ( sK6(sK10,k1_xboole_0) != k5_lattices(sK10)
% 15.07/2.51      | v13_lattices(sK10) != iProver_top ),
% 15.07/2.51      inference(demodulation,[status(thm)],[c_10274,c_3574]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(c_10336,plain,
% 15.07/2.51      ( ~ v13_lattices(sK10)
% 15.07/2.51      | sK6(sK10,k1_xboole_0) != k5_lattices(sK10) ),
% 15.07/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_10277]) ).
% 15.07/2.51  
% 15.07/2.51  cnf(contradiction,plain,
% 15.07/2.51      ( $false ),
% 15.07/2.51      inference(minisat,[status(thm)],[c_59539,c_58627,c_31038,c_10336]) ).
% 15.07/2.51  
% 15.07/2.51  
% 15.07/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.07/2.51  
% 15.07/2.51  ------                               Statistics
% 15.07/2.51  
% 15.07/2.51  ------ Selected
% 15.07/2.51  
% 15.07/2.51  total_time:                             1.848
% 15.07/2.51  
%------------------------------------------------------------------------------

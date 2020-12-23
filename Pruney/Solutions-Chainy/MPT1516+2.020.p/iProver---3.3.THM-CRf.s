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
% DateTime   : Thu Dec  3 12:19:20 EST 2020

% Result     : Theorem 39.43s
% Output     : CNFRefutation 39.43s
% Verified   : 
% Statistics : Number of formulae       :  283 (1874 expanded)
%              Number of clauses        :  191 ( 736 expanded)
%              Number of leaves         :   22 ( 333 expanded)
%              Depth                    :   25
%              Number of atoms          : 1547 (11607 expanded)
%              Number of equality atoms :  692 (3317 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f48,plain,(
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

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f73,plain,
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
   => ( ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
        | ~ l3_lattices(sK9)
        | ~ v13_lattices(sK9)
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
      & l3_lattices(sK9)
      & v4_lattice3(sK9)
      & v10_lattices(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
      | ~ l3_lattices(sK9)
      | ~ v13_lattices(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) )
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f73])).

fof(f118,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f52,plain,(
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

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = X1
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,sK2(X0),X4) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
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

fof(f34,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK6(X0)) != k2_lattices(X0,sK6(X0),X1)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK5(X0)) != k2_lattices(X0,sK5(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f64,f66,f65])).

fof(f102,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f116,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f117,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f74])).

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

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f21])).

fof(f78,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = X1
      | k2_lattices(X0,sK0(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK0(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f120,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f119,plain,
    ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
    | ~ l3_lattices(sK9)
    | ~ v13_lattices(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_666,plain,
    ( X0_62 != X1_62
    | X2_62 != X1_62
    | X2_62 = X0_62 ),
    theory(equality)).

cnf(c_2169,plain,
    ( X0_62 != X1_62
    | X0_62 = k15_lattice3(X0_61,X0_63)
    | k15_lattice3(X0_61,X0_63) != X1_62 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_33345,plain,
    ( k15_lattice3(X0_61,X0_63) != X0_62
    | k5_lattices(X0_61) != X0_62
    | k5_lattices(X0_61) = k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_135477,plain,
    ( k15_lattice3(X0_61,X0_63) != k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
    | k5_lattices(X0_61) != k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
    | k5_lattices(X0_61) = k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_33345])).

cnf(c_135481,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
    | k5_lattices(sK9) != k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
    | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_135477])).

cnf(c_22,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_641,plain,
    ( ~ r4_lattice3(X0_61,X0_62,X0_63)
    | ~ r1_lattices(X0_61,X0_62,sK4(X0_61,X0_63,X0_62))
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61)
    | k15_lattice3(X0_61,X0_63) = X0_62 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_124117,plain,
    ( ~ r4_lattice3(X0_61,sK2(X0_61),X0_63)
    | ~ r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61)))
    | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61)
    | k15_lattice3(X0_61,X0_63) = sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_124122,plain,
    ( k15_lattice3(X0_61,X0_63) = sK2(X0_61)
    | r4_lattice3(X0_61,sK2(X0_61),X0_63) != iProver_top
    | r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) != iProver_top
    | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124117])).

cnf(c_124124,plain,
    ( k15_lattice3(sK9,k1_xboole_0) = sK2(sK9)
    | r4_lattice3(sK9,sK2(sK9),k1_xboole_0) != iProver_top
    | r1_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) != iProver_top
    | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
    | v4_lattice3(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_124122])).

cnf(c_11,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_652,plain,
    ( r1_lattices(X0_61,X0_62,X1_62)
    | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ v8_lattices(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v9_lattices(X0_61)
    | k2_lattices(X0_61,X0_62,X1_62) != X0_62 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2173,plain,
    ( r1_lattices(X0_61,sK2(X0_61),X0_62)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
    | ~ v8_lattices(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v9_lattices(X0_61)
    | k2_lattices(X0_61,sK2(X0_61),X0_62) != sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_124116,plain,
    ( r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61)))
    | ~ m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61))
    | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
    | ~ v8_lattices(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v9_lattices(X0_61)
    | k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) != sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_124118,plain,
    ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) != sK2(X0_61)
    | r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) = iProver_top
    | m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
    | v8_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v9_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124116])).

cnf(c_124120,plain,
    ( k2_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) != sK2(sK9)
    | r1_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) = iProver_top
    | m1_subset_1(sK4(sK9,k1_xboole_0,sK2(sK9)),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
    | v8_lattices(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v9_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_124118])).

cnf(c_2363,plain,
    ( X0_62 != X1_62
    | k15_lattice3(X0_61,X0_63) != X1_62
    | k15_lattice3(X0_61,X0_63) = X0_62 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_4874,plain,
    ( X0_62 != sK2(X0_61)
    | k15_lattice3(X0_61,X0_63) = X0_62
    | k15_lattice3(X0_61,X0_63) != sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_33727,plain,
    ( k2_lattices(X0_61,sK2(X1_61),X0_62) != sK2(X1_61)
    | k15_lattice3(X1_61,X0_63) = k2_lattices(X0_61,sK2(X1_61),X0_62)
    | k15_lattice3(X1_61,X0_63) != sK2(X1_61) ),
    inference(instantiation,[status(thm)],[c_4874])).

cnf(c_113455,plain,
    ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) != sK2(X0_61)
    | k15_lattice3(X0_61,X0_63) = k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
    | k15_lattice3(X0_61,X0_63) != sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_33727])).

cnf(c_113456,plain,
    ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) != sK2(sK9)
    | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
    | k15_lattice3(sK9,k1_xboole_0) != sK2(sK9) ),
    inference(instantiation,[status(thm)],[c_113455])).

cnf(c_8228,plain,
    ( X0_62 != X1_62
    | k5_lattices(X0_61) != X1_62
    | k5_lattices(X0_61) = X0_62 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_12461,plain,
    ( X0_62 != k5_lattices(X0_61)
    | k5_lattices(X0_61) = X0_62
    | k5_lattices(X0_61) != k5_lattices(X0_61) ),
    inference(instantiation,[status(thm)],[c_8228])).

cnf(c_111967,plain,
    ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) != k5_lattices(X0_61)
    | k5_lattices(X0_61) = k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
    | k5_lattices(X0_61) != k5_lattices(X0_61) ),
    inference(instantiation,[status(thm)],[c_12461])).

cnf(c_111973,plain,
    ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) != k5_lattices(sK9)
    | k5_lattices(sK9) = k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_111967])).

cnf(c_41,negated_conjecture,
    ( l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_624,negated_conjecture,
    ( l3_lattices(sK9) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_1422,plain,
    ( l3_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_10,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_653,plain,
    ( l1_lattices(X0_61)
    | ~ l3_lattices(X0_61) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1393,plain,
    ( l1_lattices(X0_61) = iProver_top
    | l3_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_2081,plain,
    ( l1_lattices(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1393])).

cnf(c_17,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_646,plain,
    ( m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1400,plain,
    ( m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) = iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k5_lattices(X1) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | m1_subset_1(sK0(X0_61,X0_62),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k5_lattices(X0_61) = X0_62 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1390,plain,
    ( k5_lattices(X0_61) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(sK0(X0_61,X0_62),u1_struct_0(X0_61)) = iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,sK2(X1),X0) = sK2(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,sK2(X0_61),X0_62) = sK2(X0_61) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1399,plain,
    ( k2_lattices(X0_61,sK2(X0_61),X0_62) = sK2(X0_61)
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_3009,plain,
    ( k2_lattices(X0_61,sK2(X0_61),sK0(X0_61,X0_62)) = sK2(X0_61)
    | k5_lattices(X0_61) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1399])).

cnf(c_7010,plain,
    ( k2_lattices(X0_61,sK2(X0_61),sK0(X0_61,sK2(X0_61))) = sK2(X0_61)
    | sK2(X0_61) = k5_lattices(X0_61)
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_3009])).

cnf(c_7262,plain,
    ( k2_lattices(sK9,sK2(sK9),sK0(sK9,sK2(sK9))) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9)
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_7010])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_7263,plain,
    ( ~ v13_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,sK2(sK9),sK0(sK9,sK2(sK9))) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7262])).

cnf(c_31,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_633,plain,
    ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1413,plain,
    ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) = iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | m1_subset_1(sK1(X0_61,X0_62),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | v13_lattices(X0_61)
    | v2_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1397,plain,
    ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(sK1(X0_61,X0_62),u1_struct_0(X0_61)) = iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v6_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,X0_62,X1_62) = k2_lattices(X0_61,X1_62,X0_62) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1412,plain,
    ( k2_lattices(X0_61,X0_62,X1_62) = k2_lattices(X0_61,X1_62,X0_62)
    | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v6_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_3707,plain,
    ( k2_lattices(X0_61,sK1(X0_61,X0_62),X1_62) = k2_lattices(X0_61,X1_62,sK1(X0_61,X0_62))
    | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_1412])).

cnf(c_12098,plain,
    ( k2_lattices(X0_61,sK1(X0_61,X0_62),sK1(X0_61,X1_62)) = k2_lattices(X0_61,sK1(X0_61,X1_62),sK1(X0_61,X0_62))
    | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_3707])).

cnf(c_15917,plain,
    ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,X1_62)) = k2_lattices(X0_61,sK1(X0_61,X1_62),sK1(X0_61,sK1(X0_61,X0_62)))
    | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_12098])).

cnf(c_22532,plain,
    ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,X1_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X1_62)),sK1(X0_61,sK1(X0_61,X0_62)))
    | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_15917])).

cnf(c_35095,plain,
    ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,X0_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_22532])).

cnf(c_704,plain,
    ( l1_lattices(X0_61) = iProver_top
    | l3_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_40999,plain,
    ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,X0_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35095,c_704])).

cnf(c_41000,plain,
    ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,X0_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(renaming,[status(thm)],[c_40999])).

cnf(c_41013,plain,
    ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X1_63)))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X1_63))),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_41000])).

cnf(c_41281,plain,
    ( k2_lattices(sK9,sK1(sK9,sK1(sK9,k15_lattice3(sK9,X0_63))),sK1(sK9,sK1(sK9,k15_lattice3(sK9,X1_63)))) = k2_lattices(sK9,sK1(sK9,sK1(sK9,k15_lattice3(sK9,X1_63))),sK1(sK9,sK1(sK9,k15_lattice3(sK9,X0_63))))
    | v13_lattices(sK9) = iProver_top
    | v6_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_41013])).

cnf(c_45,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_46,plain,
    ( v10_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_47,plain,
    ( v4_lattice3(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_48,plain,
    ( l3_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_137,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_139,plain,
    ( l1_lattices(sK9) = iProver_top
    | l3_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_153,plain,
    ( v6_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_155,plain,
    ( v6_lattices(sK9) = iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_3,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_156,plain,
    ( v8_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_158,plain,
    ( v8_lattices(sK9) = iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_2,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_159,plain,
    ( l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | v9_lattices(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_161,plain,
    ( l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top
    | v9_lattices(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_756,plain,
    ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) = iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_758,plain,
    ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) = iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1991,plain,
    ( ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
    | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | v13_lattices(X0_61)
    | v2_struct_0(X0_61) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1992,plain,
    ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61)) = iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1991])).

cnf(c_1994,plain,
    ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) = iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,X0_62,sK1(X0_61,X0_62)) != X0_62
    | k2_lattices(X0_61,sK1(X0_61,X0_62),X0_62) != X0_62 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) != k15_lattice3(X0_61,X0_63)
    | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_2109,plain,
    ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) != k15_lattice3(X0_61,X0_63)
    | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != k15_lattice3(X0_61,X0_63)
    | m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2108])).

cnf(c_2111,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
    | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_19,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_644,plain,
    ( r4_lattice3(X0_61,X0_62,X0_63)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | r2_hidden(sK3(X0_61,X0_62,X0_63),X0_63)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2375,plain,
    ( r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)
    | ~ m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61))
    | r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_2386,plain,
    ( r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63) = iProver_top
    | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61)) != iProver_top
    | r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63) = iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2375])).

cnf(c_2388,plain,
    ( r4_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0) = iProver_top
    | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0),k1_xboole_0) = iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2386])).

cnf(c_25,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_638,plain,
    ( ~ r4_lattice3(X0_61,X0_62,X0_63)
    | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
    | ~ r4_lattice3(X0_61,X0_62,X0_63)
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_633])).

cnf(c_980,plain,
    ( ~ r4_lattice3(X0_61,X0_62,X0_63)
    | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61) ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_2374,plain,
    ( ~ r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)
    | r1_lattices(X0_61,k15_lattice3(X0_61,X1_63),sK1(X0_61,k15_lattice3(X0_61,X0_63)))
    | ~ m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_2390,plain,
    ( r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63) != iProver_top
    | r1_lattices(X0_61,k15_lattice3(X0_61,X1_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) = iProver_top
    | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61)) != iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2374])).

cnf(c_2392,plain,
    ( r4_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r1_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) = iProver_top
    | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top
    | v4_lattice3(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_664,plain,
    ( X0_62 = X0_62 ),
    theory(equality)).

cnf(c_2517,plain,
    ( k15_lattice3(X0_61,X0_63) = k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_2522,plain,
    ( k15_lattice3(sK9,k1_xboole_0) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_661,plain,
    ( ~ r2_hidden(X0_62,X0_63)
    | ~ r1_tarski(X0_63,X0_62) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4086,plain,
    ( ~ r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63)
    | ~ r1_tarski(X1_63,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_4092,plain,
    ( r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63) != iProver_top
    | r1_tarski(X1_63,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4086])).

cnf(c_4094,plain,
    ( r2_hidden(sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4092])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_662,plain,
    ( r1_tarski(k1_xboole_0,X0_62) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4163,plain,
    ( r1_tarski(k1_xboole_0,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_4166,plain,
    ( r1_tarski(k1_xboole_0,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4163])).

cnf(c_4168,plain,
    ( r1_tarski(k1_xboole_0,sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4166])).

cnf(c_12,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_651,plain,
    ( ~ r1_lattices(X0_61,X0_62,X1_62)
    | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ v8_lattices(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v9_lattices(X0_61)
    | k2_lattices(X0_61,X0_62,X1_62) = X0_62 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_9710,plain,
    ( ~ r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63)))
    | ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
    | ~ m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X1_63)),u1_struct_0(X0_61))
    | ~ v8_lattices(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v9_lattices(X0_61)
    | k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) = k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_9716,plain,
    ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) = k15_lattice3(X0_61,X0_63)
    | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) != iProver_top
    | m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X1_63)),u1_struct_0(X0_61)) != iProver_top
    | v8_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v9_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9710])).

cnf(c_9718,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) = k15_lattice3(sK9,k1_xboole_0)
    | r1_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != iProver_top
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top
    | v8_lattices(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v9_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9716])).

cnf(c_3702,plain,
    ( k2_lattices(X0_61,X0_62,k15_lattice3(X0_61,X0_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1412])).

cnf(c_9514,plain,
    ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | k2_lattices(X0_61,X0_62,k15_lattice3(X0_61,X0_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3702,c_704])).

cnf(c_9515,plain,
    ( k2_lattices(X0_61,X0_62,k15_lattice3(X0_61,X0_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(renaming,[status(thm)],[c_9514])).

cnf(c_9533,plain,
    ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,X0_62)) = k2_lattices(X0_61,sK1(X0_61,X0_62),k15_lattice3(X0_61,X0_63))
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_9515])).

cnf(c_13791,plain,
    ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,X0_62)) = k2_lattices(X0_61,sK1(X0_61,X0_62),k15_lattice3(X0_61,X0_63))
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9533,c_704])).

cnf(c_13792,plain,
    ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,X0_62)) = k2_lattices(X0_61,sK1(X0_61,X0_62),k15_lattice3(X0_61,X0_63))
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(renaming,[status(thm)],[c_13791])).

cnf(c_13805,plain,
    ( k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X1_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X1_63),sK1(X0_61,k15_lattice3(X0_61,X0_63)))
    | v13_lattices(X0_61) = iProver_top
    | v6_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_13792])).

cnf(c_13910,plain,
    ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0)))
    | v13_lattices(sK9) = iProver_top
    | v6_lattices(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13805])).

cnf(c_2607,plain,
    ( X0_62 != k15_lattice3(X0_61,X0_63)
    | k15_lattice3(X0_61,X1_63) = X0_62
    | k15_lattice3(X0_61,X1_63) != k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_20481,plain,
    ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) != k15_lattice3(X0_61,X0_63)
    | k15_lattice3(X0_61,X2_63) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63)))
    | k15_lattice3(X0_61,X2_63) != k15_lattice3(X0_61,X0_63) ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_20495,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
    | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0)))
    | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20481])).

cnf(c_31684,plain,
    ( k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != X0_62
    | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) = k15_lattice3(X0_61,X0_63)
    | k15_lattice3(X0_61,X0_63) != X0_62 ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_41176,plain,
    ( k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63)))
    | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) = k15_lattice3(X0_61,X0_63)
    | k15_lattice3(X0_61,X0_63) != k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) ),
    inference(instantiation,[status(thm)],[c_31684])).

cnf(c_41178,plain,
    ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0)))
    | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0)
    | k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_41176])).

cnf(c_41286,plain,
    ( v13_lattices(sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41281,c_45,c_46,c_47,c_48,c_139,c_155,c_158,c_161,c_758,c_1994,c_2111,c_2388,c_2392,c_2522,c_4094,c_4168,c_9718,c_13910,c_20495,c_41178])).

cnf(c_41288,plain,
    ( v13_lattices(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_41286])).

cnf(c_43972,plain,
    ( k2_lattices(sK9,sK2(sK9),sK0(sK9,sK2(sK9))) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7262,c_44,c_7263,c_41288])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK0(X1,X0)) != X0
    | k2_lattices(X1,sK0(X1,X0),X0) != X0
    | k5_lattices(X1) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,X0_62,sK0(X0_61,X0_62)) != X0_62
    | k2_lattices(X0_61,sK0(X0_61,X0_62),X0_62) != X0_62
    | k5_lattices(X0_61) = X0_62 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1389,plain,
    ( k2_lattices(X0_61,X0_62,sK0(X0_61,X0_62)) != X0_62
    | k2_lattices(X0_61,sK0(X0_61,X0_62),X0_62) != X0_62
    | k5_lattices(X0_61) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_43977,plain,
    ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) != sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9)
    | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_43972,c_1389])).

cnf(c_116,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v13_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_118,plain,
    ( m1_subset_1(sK2(sK9),u1_struct_0(sK9)) = iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,X0_62,sK2(X0_61)) = sK2(X0_61) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1398,plain,
    ( k2_lattices(X0_61,X0_62,sK2(X0_61)) = sK2(X0_61)
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_2994,plain,
    ( k2_lattices(X0_61,sK0(X0_61,X0_62),sK2(X0_61)) = sK2(X0_61)
    | k5_lattices(X0_61) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1398])).

cnf(c_6576,plain,
    ( k2_lattices(X0_61,sK0(X0_61,sK2(X0_61)),sK2(X0_61)) = sK2(X0_61)
    | sK2(X0_61) = k5_lattices(X0_61)
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_2994])).

cnf(c_6994,plain,
    ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9)
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_6576])).

cnf(c_6731,plain,
    ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9)
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6576])).

cnf(c_40935,plain,
    ( v13_lattices(sK9) != iProver_top
    | sK2(sK9) = k5_lattices(sK9)
    | k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6994,c_45,c_48,c_139,c_6731])).

cnf(c_40936,plain,
    ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9)
    | v13_lattices(sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_40935])).

cnf(c_41291,plain,
    ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
    | sK2(sK9) = k5_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_41286,c_40936])).

cnf(c_44009,plain,
    ( sK2(sK9) = k5_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_43977,c_45,c_46,c_47,c_48,c_118,c_139,c_155,c_158,c_161,c_758,c_1994,c_2111,c_2388,c_2392,c_2522,c_4094,c_4168,c_9718,c_13910,c_20495,c_41178,c_41291])).

cnf(c_44020,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_44009,c_1400])).

cnf(c_1384,plain,
    ( r1_tarski(k1_xboole_0,X0_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1402,plain,
    ( r4_lattice3(X0_61,X0_62,X0_63) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | r2_hidden(sK3(X0_61,X0_62,X0_63),X0_63) = iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1385,plain,
    ( r2_hidden(X0_62,X0_63) != iProver_top
    | r1_tarski(X0_63,X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_3147,plain,
    ( r4_lattice3(X0_61,X0_62,X0_63) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | r1_tarski(X0_63,sK3(X0_61,X0_62,X0_63)) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_1385])).

cnf(c_6232,plain,
    ( r4_lattice3(X0_61,X0_62,k1_xboole_0) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_3147])).

cnf(c_6348,plain,
    ( r4_lattice3(X0_61,sK2(X0_61),k1_xboole_0) = iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_6232])).

cnf(c_6837,plain,
    ( r4_lattice3(X0_61,sK2(X0_61),k1_xboole_0) = iProver_top
    | v13_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6348,c_704])).

cnf(c_24,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_639,plain,
    ( ~ r4_lattice3(X0_61,X0_62,X0_63)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | m1_subset_1(sK4(X0_61,X0_63,X0_62),u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61)
    | k15_lattice3(X0_61,X0_63) = X0_62 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1407,plain,
    ( k15_lattice3(X0_61,X0_63) = X0_62
    | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(sK4(X0_61,X0_63,X0_62),u1_struct_0(X0_61)) = iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_4919,plain,
    ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,X0_62)) = sK2(X0_61)
    | k15_lattice3(X0_61,X0_63) = X0_62
    | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_1399])).

cnf(c_22904,plain,
    ( v4_lattice3(X0_61) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
    | k15_lattice3(X0_61,X0_63) = X0_62
    | k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,X0_62)) = sK2(X0_61)
    | v13_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4919,c_704])).

cnf(c_22905,plain,
    ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,X0_62)) = sK2(X0_61)
    | k15_lattice3(X0_61,X0_63) = X0_62
    | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(renaming,[status(thm)],[c_22904])).

cnf(c_22940,plain,
    ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,k1_xboole_0,sK2(X0_61))) = sK2(X0_61)
    | k15_lattice3(X0_61,k1_xboole_0) = sK2(X0_61)
    | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_6837,c_22905])).

cnf(c_23476,plain,
    ( k2_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) = sK2(sK9)
    | k15_lattice3(sK9,k1_xboole_0) = sK2(sK9)
    | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
    | v4_lattice3(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22940])).

cnf(c_12462,plain,
    ( k5_lattices(X0_61) = k5_lattices(X0_61) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_12464,plain,
    ( k5_lattices(sK9) = k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_12462])).

cnf(c_6473,plain,
    ( r4_lattice3(sK9,sK2(sK9),k1_xboole_0) = iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6348])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,X0_62,k5_lattices(X0_61)) = k5_lattices(X0_61) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4595,plain,
    ( ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
    | ~ m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = k5_lattices(X0_61) ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_4596,plain,
    ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = k5_lattices(X0_61)
    | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
    | m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4595])).

cnf(c_4598,plain,
    ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) = k5_lattices(sK9)
    | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) != iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4596])).

cnf(c_4435,plain,
    ( ~ m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61))
    | ~ l1_lattices(X0_61)
    | ~ v13_lattices(X0_61)
    | v2_struct_0(X0_61)
    | k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_4476,plain,
    ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = sK2(X0_61)
    | m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61)) != iProver_top
    | l1_lattices(X0_61) != iProver_top
    | v13_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4435])).

cnf(c_4478,plain,
    ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) = sK2(sK9)
    | m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) != iProver_top
    | l1_lattices(sK9) != iProver_top
    | v13_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4476])).

cnf(c_2172,plain,
    ( ~ r4_lattice3(X0_61,sK2(X0_61),X0_63)
    | m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61))
    | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
    | ~ v4_lattice3(X0_61)
    | ~ l3_lattices(X0_61)
    | v2_struct_0(X0_61)
    | ~ v10_lattices(X0_61)
    | k15_lattice3(X0_61,X0_63) = sK2(X0_61) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_2203,plain,
    ( k15_lattice3(X0_61,X0_63) = sK2(X0_61)
    | r4_lattice3(X0_61,sK2(X0_61),X0_63) != iProver_top
    | m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61)) = iProver_top
    | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
    | v4_lattice3(X0_61) != iProver_top
    | l3_lattices(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | v10_lattices(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_2205,plain,
    ( k15_lattice3(sK9,k1_xboole_0) = sK2(sK9)
    | r4_lattice3(sK9,sK2(sK9),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4(sK9,k1_xboole_0,sK2(sK9)),u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
    | v4_lattice3(sK9) != iProver_top
    | l3_lattices(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v10_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_40,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_335,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40,c_44,c_43,c_41])).

cnf(c_620,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_335])).

cnf(c_787,plain,
    ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135481,c_124124,c_124120,c_113456,c_111973,c_44020,c_41286,c_23476,c_12464,c_6473,c_4598,c_4478,c_2205,c_787,c_161,c_158,c_139,c_118,c_48,c_47,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:16:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.43/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.43/5.49  
% 39.43/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.43/5.49  
% 39.43/5.49  ------  iProver source info
% 39.43/5.49  
% 39.43/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.43/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.43/5.49  git: non_committed_changes: false
% 39.43/5.49  git: last_make_outside_of_git: false
% 39.43/5.49  
% 39.43/5.49  ------ 
% 39.43/5.49  
% 39.43/5.49  ------ Input Options
% 39.43/5.49  
% 39.43/5.49  --out_options                           all
% 39.43/5.49  --tptp_safe_out                         true
% 39.43/5.49  --problem_path                          ""
% 39.43/5.49  --include_path                          ""
% 39.43/5.49  --clausifier                            res/vclausify_rel
% 39.43/5.49  --clausifier_options                    --mode clausify
% 39.43/5.49  --stdin                                 false
% 39.43/5.49  --stats_out                             sel
% 39.43/5.49  
% 39.43/5.49  ------ General Options
% 39.43/5.49  
% 39.43/5.49  --fof                                   false
% 39.43/5.49  --time_out_real                         604.99
% 39.43/5.49  --time_out_virtual                      -1.
% 39.43/5.49  --symbol_type_check                     false
% 39.43/5.49  --clausify_out                          false
% 39.43/5.49  --sig_cnt_out                           false
% 39.43/5.49  --trig_cnt_out                          false
% 39.43/5.49  --trig_cnt_out_tolerance                1.
% 39.43/5.49  --trig_cnt_out_sk_spl                   false
% 39.43/5.49  --abstr_cl_out                          false
% 39.43/5.49  
% 39.43/5.49  ------ Global Options
% 39.43/5.49  
% 39.43/5.49  --schedule                              none
% 39.43/5.49  --add_important_lit                     false
% 39.43/5.49  --prop_solver_per_cl                    1000
% 39.43/5.49  --min_unsat_core                        false
% 39.43/5.49  --soft_assumptions                      false
% 39.43/5.49  --soft_lemma_size                       3
% 39.43/5.49  --prop_impl_unit_size                   0
% 39.43/5.49  --prop_impl_unit                        []
% 39.43/5.49  --share_sel_clauses                     true
% 39.43/5.49  --reset_solvers                         false
% 39.43/5.49  --bc_imp_inh                            [conj_cone]
% 39.43/5.49  --conj_cone_tolerance                   3.
% 39.43/5.49  --extra_neg_conj                        none
% 39.43/5.49  --large_theory_mode                     true
% 39.43/5.49  --prolific_symb_bound                   200
% 39.43/5.49  --lt_threshold                          2000
% 39.43/5.49  --clause_weak_htbl                      true
% 39.43/5.49  --gc_record_bc_elim                     false
% 39.43/5.49  
% 39.43/5.49  ------ Preprocessing Options
% 39.43/5.49  
% 39.43/5.49  --preprocessing_flag                    true
% 39.43/5.49  --time_out_prep_mult                    0.1
% 39.43/5.49  --splitting_mode                        input
% 39.43/5.49  --splitting_grd                         true
% 39.43/5.49  --splitting_cvd                         false
% 39.43/5.49  --splitting_cvd_svl                     false
% 39.43/5.49  --splitting_nvd                         32
% 39.43/5.49  --sub_typing                            true
% 39.43/5.49  --prep_gs_sim                           false
% 39.43/5.49  --prep_unflatten                        true
% 39.43/5.49  --prep_res_sim                          true
% 39.43/5.49  --prep_upred                            true
% 39.43/5.49  --prep_sem_filter                       exhaustive
% 39.43/5.49  --prep_sem_filter_out                   false
% 39.43/5.49  --pred_elim                             false
% 39.43/5.49  --res_sim_input                         true
% 39.43/5.49  --eq_ax_congr_red                       true
% 39.43/5.49  --pure_diseq_elim                       true
% 39.43/5.49  --brand_transform                       false
% 39.43/5.49  --non_eq_to_eq                          false
% 39.43/5.49  --prep_def_merge                        true
% 39.43/5.49  --prep_def_merge_prop_impl              false
% 39.43/5.49  --prep_def_merge_mbd                    true
% 39.43/5.49  --prep_def_merge_tr_red                 false
% 39.43/5.49  --prep_def_merge_tr_cl                  false
% 39.43/5.49  --smt_preprocessing                     true
% 39.43/5.49  --smt_ac_axioms                         fast
% 39.43/5.49  --preprocessed_out                      false
% 39.43/5.49  --preprocessed_stats                    false
% 39.43/5.49  
% 39.43/5.49  ------ Abstraction refinement Options
% 39.43/5.49  
% 39.43/5.49  --abstr_ref                             []
% 39.43/5.49  --abstr_ref_prep                        false
% 39.43/5.49  --abstr_ref_until_sat                   false
% 39.43/5.49  --abstr_ref_sig_restrict                funpre
% 39.43/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.43/5.49  --abstr_ref_under                       []
% 39.43/5.49  
% 39.43/5.49  ------ SAT Options
% 39.43/5.49  
% 39.43/5.49  --sat_mode                              false
% 39.43/5.49  --sat_fm_restart_options                ""
% 39.43/5.49  --sat_gr_def                            false
% 39.43/5.49  --sat_epr_types                         true
% 39.43/5.49  --sat_non_cyclic_types                  false
% 39.43/5.49  --sat_finite_models                     false
% 39.43/5.49  --sat_fm_lemmas                         false
% 39.43/5.49  --sat_fm_prep                           false
% 39.43/5.49  --sat_fm_uc_incr                        true
% 39.43/5.49  --sat_out_model                         small
% 39.43/5.49  --sat_out_clauses                       false
% 39.43/5.49  
% 39.43/5.49  ------ QBF Options
% 39.43/5.49  
% 39.43/5.49  --qbf_mode                              false
% 39.43/5.49  --qbf_elim_univ                         false
% 39.43/5.49  --qbf_dom_inst                          none
% 39.43/5.49  --qbf_dom_pre_inst                      false
% 39.43/5.49  --qbf_sk_in                             false
% 39.43/5.49  --qbf_pred_elim                         true
% 39.43/5.49  --qbf_split                             512
% 39.43/5.49  
% 39.43/5.49  ------ BMC1 Options
% 39.43/5.49  
% 39.43/5.49  --bmc1_incremental                      false
% 39.43/5.49  --bmc1_axioms                           reachable_all
% 39.43/5.49  --bmc1_min_bound                        0
% 39.43/5.49  --bmc1_max_bound                        -1
% 39.43/5.49  --bmc1_max_bound_default                -1
% 39.43/5.49  --bmc1_symbol_reachability              true
% 39.43/5.49  --bmc1_property_lemmas                  false
% 39.43/5.49  --bmc1_k_induction                      false
% 39.43/5.49  --bmc1_non_equiv_states                 false
% 39.43/5.49  --bmc1_deadlock                         false
% 39.43/5.49  --bmc1_ucm                              false
% 39.43/5.49  --bmc1_add_unsat_core                   none
% 39.43/5.49  --bmc1_unsat_core_children              false
% 39.43/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.43/5.49  --bmc1_out_stat                         full
% 39.43/5.49  --bmc1_ground_init                      false
% 39.43/5.49  --bmc1_pre_inst_next_state              false
% 39.43/5.49  --bmc1_pre_inst_state                   false
% 39.43/5.49  --bmc1_pre_inst_reach_state             false
% 39.43/5.49  --bmc1_out_unsat_core                   false
% 39.43/5.49  --bmc1_aig_witness_out                  false
% 39.43/5.49  --bmc1_verbose                          false
% 39.43/5.49  --bmc1_dump_clauses_tptp                false
% 39.43/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.43/5.49  --bmc1_dump_file                        -
% 39.43/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.43/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.43/5.49  --bmc1_ucm_extend_mode                  1
% 39.43/5.49  --bmc1_ucm_init_mode                    2
% 39.43/5.49  --bmc1_ucm_cone_mode                    none
% 39.43/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.43/5.49  --bmc1_ucm_relax_model                  4
% 39.43/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.43/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.43/5.49  --bmc1_ucm_layered_model                none
% 39.43/5.49  --bmc1_ucm_max_lemma_size               10
% 39.43/5.49  
% 39.43/5.49  ------ AIG Options
% 39.43/5.49  
% 39.43/5.49  --aig_mode                              false
% 39.43/5.49  
% 39.43/5.49  ------ Instantiation Options
% 39.43/5.49  
% 39.43/5.49  --instantiation_flag                    true
% 39.43/5.49  --inst_sos_flag                         false
% 39.43/5.49  --inst_sos_phase                        true
% 39.43/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.43/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.43/5.49  --inst_lit_sel_side                     num_symb
% 39.43/5.49  --inst_solver_per_active                1400
% 39.43/5.49  --inst_solver_calls_frac                1.
% 39.43/5.49  --inst_passive_queue_type               priority_queues
% 39.43/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.43/5.49  --inst_passive_queues_freq              [25;2]
% 39.43/5.49  --inst_dismatching                      true
% 39.43/5.49  --inst_eager_unprocessed_to_passive     true
% 39.43/5.49  --inst_prop_sim_given                   true
% 39.43/5.49  --inst_prop_sim_new                     false
% 39.43/5.49  --inst_subs_new                         false
% 39.43/5.49  --inst_eq_res_simp                      false
% 39.43/5.49  --inst_subs_given                       false
% 39.43/5.49  --inst_orphan_elimination               true
% 39.43/5.49  --inst_learning_loop_flag               true
% 39.43/5.49  --inst_learning_start                   3000
% 39.43/5.49  --inst_learning_factor                  2
% 39.43/5.49  --inst_start_prop_sim_after_learn       3
% 39.43/5.49  --inst_sel_renew                        solver
% 39.43/5.49  --inst_lit_activity_flag                true
% 39.43/5.49  --inst_restr_to_given                   false
% 39.43/5.49  --inst_activity_threshold               500
% 39.43/5.49  --inst_out_proof                        true
% 39.43/5.49  
% 39.43/5.49  ------ Resolution Options
% 39.43/5.49  
% 39.43/5.49  --resolution_flag                       true
% 39.43/5.49  --res_lit_sel                           adaptive
% 39.43/5.49  --res_lit_sel_side                      none
% 39.43/5.49  --res_ordering                          kbo
% 39.43/5.49  --res_to_prop_solver                    active
% 39.43/5.49  --res_prop_simpl_new                    false
% 39.43/5.49  --res_prop_simpl_given                  true
% 39.43/5.49  --res_passive_queue_type                priority_queues
% 39.43/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.43/5.49  --res_passive_queues_freq               [15;5]
% 39.43/5.49  --res_forward_subs                      full
% 39.43/5.49  --res_backward_subs                     full
% 39.43/5.49  --res_forward_subs_resolution           true
% 39.43/5.49  --res_backward_subs_resolution          true
% 39.43/5.49  --res_orphan_elimination                true
% 39.43/5.49  --res_time_limit                        2.
% 39.43/5.49  --res_out_proof                         true
% 39.43/5.49  
% 39.43/5.49  ------ Superposition Options
% 39.43/5.49  
% 39.43/5.49  --superposition_flag                    true
% 39.43/5.49  --sup_passive_queue_type                priority_queues
% 39.43/5.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.43/5.49  --sup_passive_queues_freq               [1;4]
% 39.43/5.49  --demod_completeness_check              fast
% 39.43/5.49  --demod_use_ground                      true
% 39.43/5.49  --sup_to_prop_solver                    passive
% 39.43/5.49  --sup_prop_simpl_new                    true
% 39.43/5.49  --sup_prop_simpl_given                  true
% 39.43/5.49  --sup_fun_splitting                     false
% 39.43/5.49  --sup_smt_interval                      50000
% 39.43/5.49  
% 39.43/5.49  ------ Superposition Simplification Setup
% 39.43/5.49  
% 39.43/5.49  --sup_indices_passive                   []
% 39.43/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.43/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.43/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.43/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.43/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.43/5.49  --sup_full_bw                           [BwDemod]
% 39.43/5.49  --sup_immed_triv                        [TrivRules]
% 39.43/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.43/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.43/5.49  --sup_immed_bw_main                     []
% 39.43/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.43/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.43/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.43/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.43/5.49  
% 39.43/5.49  ------ Combination Options
% 39.43/5.49  
% 39.43/5.49  --comb_res_mult                         3
% 39.43/5.49  --comb_sup_mult                         2
% 39.43/5.49  --comb_inst_mult                        10
% 39.43/5.49  
% 39.43/5.49  ------ Debug Options
% 39.43/5.49  
% 39.43/5.49  --dbg_backtrace                         false
% 39.43/5.49  --dbg_dump_prop_clauses                 false
% 39.43/5.49  --dbg_dump_prop_clauses_file            -
% 39.43/5.49  --dbg_out_stat                          false
% 39.43/5.49  ------ Parsing...
% 39.43/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.43/5.49  
% 39.43/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.43/5.49  
% 39.43/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.43/5.49  
% 39.43/5.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.43/5.49  ------ Proving...
% 39.43/5.49  ------ Problem Properties 
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  clauses                                 44
% 39.43/5.49  conjectures                             5
% 39.43/5.49  EPR                                     10
% 39.43/5.49  Horn                                    8
% 39.43/5.49  unary                                   5
% 39.43/5.49  binary                                  3
% 39.43/5.49  lits                                    218
% 39.43/5.49  lits eq                                 21
% 39.43/5.49  fd_pure                                 0
% 39.43/5.49  fd_pseudo                               0
% 39.43/5.49  fd_cond                                 0
% 39.43/5.49  fd_pseudo_cond                          5
% 39.43/5.49  AC symbols                              0
% 39.43/5.49  
% 39.43/5.49  ------ Input Options Time Limit: Unbounded
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  ------ 
% 39.43/5.49  Current options:
% 39.43/5.49  ------ 
% 39.43/5.49  
% 39.43/5.49  ------ Input Options
% 39.43/5.49  
% 39.43/5.49  --out_options                           all
% 39.43/5.49  --tptp_safe_out                         true
% 39.43/5.49  --problem_path                          ""
% 39.43/5.49  --include_path                          ""
% 39.43/5.49  --clausifier                            res/vclausify_rel
% 39.43/5.49  --clausifier_options                    --mode clausify
% 39.43/5.49  --stdin                                 false
% 39.43/5.49  --stats_out                             sel
% 39.43/5.49  
% 39.43/5.49  ------ General Options
% 39.43/5.49  
% 39.43/5.49  --fof                                   false
% 39.43/5.49  --time_out_real                         604.99
% 39.43/5.49  --time_out_virtual                      -1.
% 39.43/5.49  --symbol_type_check                     false
% 39.43/5.49  --clausify_out                          false
% 39.43/5.49  --sig_cnt_out                           false
% 39.43/5.49  --trig_cnt_out                          false
% 39.43/5.49  --trig_cnt_out_tolerance                1.
% 39.43/5.49  --trig_cnt_out_sk_spl                   false
% 39.43/5.49  --abstr_cl_out                          false
% 39.43/5.49  
% 39.43/5.49  ------ Global Options
% 39.43/5.49  
% 39.43/5.49  --schedule                              none
% 39.43/5.49  --add_important_lit                     false
% 39.43/5.49  --prop_solver_per_cl                    1000
% 39.43/5.49  --min_unsat_core                        false
% 39.43/5.49  --soft_assumptions                      false
% 39.43/5.49  --soft_lemma_size                       3
% 39.43/5.49  --prop_impl_unit_size                   0
% 39.43/5.49  --prop_impl_unit                        []
% 39.43/5.49  --share_sel_clauses                     true
% 39.43/5.49  --reset_solvers                         false
% 39.43/5.49  --bc_imp_inh                            [conj_cone]
% 39.43/5.49  --conj_cone_tolerance                   3.
% 39.43/5.49  --extra_neg_conj                        none
% 39.43/5.49  --large_theory_mode                     true
% 39.43/5.49  --prolific_symb_bound                   200
% 39.43/5.49  --lt_threshold                          2000
% 39.43/5.49  --clause_weak_htbl                      true
% 39.43/5.49  --gc_record_bc_elim                     false
% 39.43/5.49  
% 39.43/5.49  ------ Preprocessing Options
% 39.43/5.49  
% 39.43/5.49  --preprocessing_flag                    true
% 39.43/5.49  --time_out_prep_mult                    0.1
% 39.43/5.49  --splitting_mode                        input
% 39.43/5.49  --splitting_grd                         true
% 39.43/5.49  --splitting_cvd                         false
% 39.43/5.49  --splitting_cvd_svl                     false
% 39.43/5.49  --splitting_nvd                         32
% 39.43/5.49  --sub_typing                            true
% 39.43/5.49  --prep_gs_sim                           false
% 39.43/5.49  --prep_unflatten                        true
% 39.43/5.49  --prep_res_sim                          true
% 39.43/5.49  --prep_upred                            true
% 39.43/5.49  --prep_sem_filter                       exhaustive
% 39.43/5.49  --prep_sem_filter_out                   false
% 39.43/5.49  --pred_elim                             false
% 39.43/5.49  --res_sim_input                         true
% 39.43/5.49  --eq_ax_congr_red                       true
% 39.43/5.49  --pure_diseq_elim                       true
% 39.43/5.49  --brand_transform                       false
% 39.43/5.49  --non_eq_to_eq                          false
% 39.43/5.49  --prep_def_merge                        true
% 39.43/5.49  --prep_def_merge_prop_impl              false
% 39.43/5.49  --prep_def_merge_mbd                    true
% 39.43/5.49  --prep_def_merge_tr_red                 false
% 39.43/5.49  --prep_def_merge_tr_cl                  false
% 39.43/5.49  --smt_preprocessing                     true
% 39.43/5.49  --smt_ac_axioms                         fast
% 39.43/5.49  --preprocessed_out                      false
% 39.43/5.49  --preprocessed_stats                    false
% 39.43/5.49  
% 39.43/5.49  ------ Abstraction refinement Options
% 39.43/5.49  
% 39.43/5.49  --abstr_ref                             []
% 39.43/5.49  --abstr_ref_prep                        false
% 39.43/5.49  --abstr_ref_until_sat                   false
% 39.43/5.49  --abstr_ref_sig_restrict                funpre
% 39.43/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.43/5.49  --abstr_ref_under                       []
% 39.43/5.49  
% 39.43/5.49  ------ SAT Options
% 39.43/5.49  
% 39.43/5.49  --sat_mode                              false
% 39.43/5.49  --sat_fm_restart_options                ""
% 39.43/5.49  --sat_gr_def                            false
% 39.43/5.49  --sat_epr_types                         true
% 39.43/5.49  --sat_non_cyclic_types                  false
% 39.43/5.49  --sat_finite_models                     false
% 39.43/5.49  --sat_fm_lemmas                         false
% 39.43/5.49  --sat_fm_prep                           false
% 39.43/5.49  --sat_fm_uc_incr                        true
% 39.43/5.49  --sat_out_model                         small
% 39.43/5.49  --sat_out_clauses                       false
% 39.43/5.49  
% 39.43/5.49  ------ QBF Options
% 39.43/5.49  
% 39.43/5.49  --qbf_mode                              false
% 39.43/5.49  --qbf_elim_univ                         false
% 39.43/5.49  --qbf_dom_inst                          none
% 39.43/5.49  --qbf_dom_pre_inst                      false
% 39.43/5.49  --qbf_sk_in                             false
% 39.43/5.49  --qbf_pred_elim                         true
% 39.43/5.49  --qbf_split                             512
% 39.43/5.49  
% 39.43/5.49  ------ BMC1 Options
% 39.43/5.49  
% 39.43/5.49  --bmc1_incremental                      false
% 39.43/5.49  --bmc1_axioms                           reachable_all
% 39.43/5.49  --bmc1_min_bound                        0
% 39.43/5.49  --bmc1_max_bound                        -1
% 39.43/5.49  --bmc1_max_bound_default                -1
% 39.43/5.49  --bmc1_symbol_reachability              true
% 39.43/5.49  --bmc1_property_lemmas                  false
% 39.43/5.49  --bmc1_k_induction                      false
% 39.43/5.49  --bmc1_non_equiv_states                 false
% 39.43/5.49  --bmc1_deadlock                         false
% 39.43/5.49  --bmc1_ucm                              false
% 39.43/5.49  --bmc1_add_unsat_core                   none
% 39.43/5.49  --bmc1_unsat_core_children              false
% 39.43/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.43/5.49  --bmc1_out_stat                         full
% 39.43/5.49  --bmc1_ground_init                      false
% 39.43/5.49  --bmc1_pre_inst_next_state              false
% 39.43/5.49  --bmc1_pre_inst_state                   false
% 39.43/5.49  --bmc1_pre_inst_reach_state             false
% 39.43/5.49  --bmc1_out_unsat_core                   false
% 39.43/5.49  --bmc1_aig_witness_out                  false
% 39.43/5.49  --bmc1_verbose                          false
% 39.43/5.49  --bmc1_dump_clauses_tptp                false
% 39.43/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.43/5.49  --bmc1_dump_file                        -
% 39.43/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.43/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.43/5.49  --bmc1_ucm_extend_mode                  1
% 39.43/5.49  --bmc1_ucm_init_mode                    2
% 39.43/5.49  --bmc1_ucm_cone_mode                    none
% 39.43/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.43/5.49  --bmc1_ucm_relax_model                  4
% 39.43/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.43/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.43/5.49  --bmc1_ucm_layered_model                none
% 39.43/5.49  --bmc1_ucm_max_lemma_size               10
% 39.43/5.49  
% 39.43/5.49  ------ AIG Options
% 39.43/5.49  
% 39.43/5.49  --aig_mode                              false
% 39.43/5.49  
% 39.43/5.49  ------ Instantiation Options
% 39.43/5.49  
% 39.43/5.49  --instantiation_flag                    true
% 39.43/5.49  --inst_sos_flag                         false
% 39.43/5.49  --inst_sos_phase                        true
% 39.43/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.43/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.43/5.49  --inst_lit_sel_side                     num_symb
% 39.43/5.49  --inst_solver_per_active                1400
% 39.43/5.49  --inst_solver_calls_frac                1.
% 39.43/5.49  --inst_passive_queue_type               priority_queues
% 39.43/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.43/5.49  --inst_passive_queues_freq              [25;2]
% 39.43/5.49  --inst_dismatching                      true
% 39.43/5.49  --inst_eager_unprocessed_to_passive     true
% 39.43/5.49  --inst_prop_sim_given                   true
% 39.43/5.49  --inst_prop_sim_new                     false
% 39.43/5.49  --inst_subs_new                         false
% 39.43/5.49  --inst_eq_res_simp                      false
% 39.43/5.49  --inst_subs_given                       false
% 39.43/5.49  --inst_orphan_elimination               true
% 39.43/5.49  --inst_learning_loop_flag               true
% 39.43/5.49  --inst_learning_start                   3000
% 39.43/5.49  --inst_learning_factor                  2
% 39.43/5.49  --inst_start_prop_sim_after_learn       3
% 39.43/5.49  --inst_sel_renew                        solver
% 39.43/5.49  --inst_lit_activity_flag                true
% 39.43/5.49  --inst_restr_to_given                   false
% 39.43/5.49  --inst_activity_threshold               500
% 39.43/5.49  --inst_out_proof                        true
% 39.43/5.49  
% 39.43/5.49  ------ Resolution Options
% 39.43/5.49  
% 39.43/5.49  --resolution_flag                       true
% 39.43/5.49  --res_lit_sel                           adaptive
% 39.43/5.49  --res_lit_sel_side                      none
% 39.43/5.49  --res_ordering                          kbo
% 39.43/5.49  --res_to_prop_solver                    active
% 39.43/5.49  --res_prop_simpl_new                    false
% 39.43/5.49  --res_prop_simpl_given                  true
% 39.43/5.49  --res_passive_queue_type                priority_queues
% 39.43/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.43/5.49  --res_passive_queues_freq               [15;5]
% 39.43/5.49  --res_forward_subs                      full
% 39.43/5.49  --res_backward_subs                     full
% 39.43/5.49  --res_forward_subs_resolution           true
% 39.43/5.49  --res_backward_subs_resolution          true
% 39.43/5.49  --res_orphan_elimination                true
% 39.43/5.49  --res_time_limit                        2.
% 39.43/5.49  --res_out_proof                         true
% 39.43/5.49  
% 39.43/5.49  ------ Superposition Options
% 39.43/5.49  
% 39.43/5.49  --superposition_flag                    true
% 39.43/5.49  --sup_passive_queue_type                priority_queues
% 39.43/5.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.43/5.49  --sup_passive_queues_freq               [1;4]
% 39.43/5.49  --demod_completeness_check              fast
% 39.43/5.49  --demod_use_ground                      true
% 39.43/5.49  --sup_to_prop_solver                    passive
% 39.43/5.49  --sup_prop_simpl_new                    true
% 39.43/5.49  --sup_prop_simpl_given                  true
% 39.43/5.49  --sup_fun_splitting                     false
% 39.43/5.49  --sup_smt_interval                      50000
% 39.43/5.49  
% 39.43/5.49  ------ Superposition Simplification Setup
% 39.43/5.49  
% 39.43/5.49  --sup_indices_passive                   []
% 39.43/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.43/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.43/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.43/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.43/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.43/5.49  --sup_full_bw                           [BwDemod]
% 39.43/5.49  --sup_immed_triv                        [TrivRules]
% 39.43/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.43/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.43/5.49  --sup_immed_bw_main                     []
% 39.43/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.43/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.43/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.43/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.43/5.49  
% 39.43/5.49  ------ Combination Options
% 39.43/5.49  
% 39.43/5.49  --comb_res_mult                         3
% 39.43/5.49  --comb_sup_mult                         2
% 39.43/5.49  --comb_inst_mult                        10
% 39.43/5.49  
% 39.43/5.49  ------ Debug Options
% 39.43/5.49  
% 39.43/5.49  --dbg_backtrace                         false
% 39.43/5.49  --dbg_dump_prop_clauses                 false
% 39.43/5.49  --dbg_dump_prop_clauses_file            -
% 39.43/5.49  --dbg_out_stat                          false
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  ------ Proving...
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  % SZS status Theorem for theBenchmark.p
% 39.43/5.49  
% 39.43/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.43/5.49  
% 39.43/5.49  fof(f9,axiom,(
% 39.43/5.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f32,plain,(
% 39.43/5.49    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f9])).
% 39.43/5.49  
% 39.43/5.49  fof(f33,plain,(
% 39.43/5.49    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f32])).
% 39.43/5.49  
% 39.43/5.49  fof(f58,plain,(
% 39.43/5.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(nnf_transformation,[],[f33])).
% 39.43/5.49  
% 39.43/5.49  fof(f59,plain,(
% 39.43/5.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f58])).
% 39.43/5.49  
% 39.43/5.49  fof(f60,plain,(
% 39.43/5.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(rectify,[],[f59])).
% 39.43/5.49  
% 39.43/5.49  fof(f61,plain,(
% 39.43/5.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f62,plain,(
% 39.43/5.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 39.43/5.49  
% 39.43/5.49  fof(f101,plain,(
% 39.43/5.49    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f62])).
% 39.43/5.49  
% 39.43/5.49  fof(f6,axiom,(
% 39.43/5.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f26,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f6])).
% 39.43/5.49  
% 39.43/5.49  fof(f27,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f26])).
% 39.43/5.49  
% 39.43/5.49  fof(f48,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(nnf_transformation,[],[f27])).
% 39.43/5.49  
% 39.43/5.49  fof(f87,plain,(
% 39.43/5.49    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f48])).
% 39.43/5.49  
% 39.43/5.49  fof(f14,conjecture,(
% 39.43/5.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f15,negated_conjecture,(
% 39.43/5.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 39.43/5.49    inference(negated_conjecture,[],[f14])).
% 39.43/5.49  
% 39.43/5.49  fof(f42,plain,(
% 39.43/5.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f15])).
% 39.43/5.49  
% 39.43/5.49  fof(f43,plain,(
% 39.43/5.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f42])).
% 39.43/5.49  
% 39.43/5.49  fof(f73,plain,(
% 39.43/5.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f74,plain,(
% 39.43/5.49    (k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 39.43/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f73])).
% 39.43/5.49  
% 39.43/5.49  fof(f118,plain,(
% 39.43/5.49    l3_lattices(sK9)),
% 39.43/5.49    inference(cnf_transformation,[],[f74])).
% 39.43/5.49  
% 39.43/5.49  fof(f5,axiom,(
% 39.43/5.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f16,plain,(
% 39.43/5.49    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 39.43/5.49    inference(pure_predicate_removal,[],[f5])).
% 39.43/5.49  
% 39.43/5.49  fof(f25,plain,(
% 39.43/5.49    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 39.43/5.49    inference(ennf_transformation,[],[f16])).
% 39.43/5.49  
% 39.43/5.49  fof(f85,plain,(
% 39.43/5.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f25])).
% 39.43/5.49  
% 39.43/5.49  fof(f7,axiom,(
% 39.43/5.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f28,plain,(
% 39.43/5.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f7])).
% 39.43/5.49  
% 39.43/5.49  fof(f29,plain,(
% 39.43/5.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f28])).
% 39.43/5.49  
% 39.43/5.49  fof(f49,plain,(
% 39.43/5.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(nnf_transformation,[],[f29])).
% 39.43/5.49  
% 39.43/5.49  fof(f50,plain,(
% 39.43/5.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(rectify,[],[f49])).
% 39.43/5.49  
% 39.43/5.49  fof(f52,plain,(
% 39.43/5.49    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f51,plain,(
% 39.43/5.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f53,plain,(
% 39.43/5.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).
% 39.43/5.49  
% 39.43/5.49  fof(f88,plain,(
% 39.43/5.49    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f53])).
% 39.43/5.49  
% 39.43/5.49  fof(f4,axiom,(
% 39.43/5.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f23,plain,(
% 39.43/5.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f4])).
% 39.43/5.49  
% 39.43/5.49  fof(f24,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f23])).
% 39.43/5.49  
% 39.43/5.49  fof(f44,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(nnf_transformation,[],[f24])).
% 39.43/5.49  
% 39.43/5.49  fof(f45,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(rectify,[],[f44])).
% 39.43/5.49  
% 39.43/5.49  fof(f46,plain,(
% 39.43/5.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f47,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 39.43/5.49  
% 39.43/5.49  fof(f83,plain,(
% 39.43/5.49    ( ! [X0,X1] : (k5_lattices(X0) = X1 | m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f47])).
% 39.43/5.49  
% 39.43/5.49  fof(f89,plain,(
% 39.43/5.49    ( ! [X4,X0] : (k2_lattices(X0,sK2(X0),X4) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f53])).
% 39.43/5.49  
% 39.43/5.49  fof(f115,plain,(
% 39.43/5.49    ~v2_struct_0(sK9)),
% 39.43/5.49    inference(cnf_transformation,[],[f74])).
% 39.43/5.49  
% 39.43/5.49  fof(f11,axiom,(
% 39.43/5.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f36,plain,(
% 39.43/5.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f11])).
% 39.43/5.49  
% 39.43/5.49  fof(f37,plain,(
% 39.43/5.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f36])).
% 39.43/5.49  
% 39.43/5.49  fof(f106,plain,(
% 39.43/5.49    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f37])).
% 39.43/5.49  
% 39.43/5.49  fof(f91,plain,(
% 39.43/5.49    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f53])).
% 39.43/5.49  
% 39.43/5.49  fof(f10,axiom,(
% 39.43/5.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f34,plain,(
% 39.43/5.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f10])).
% 39.43/5.49  
% 39.43/5.49  fof(f35,plain,(
% 39.43/5.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f34])).
% 39.43/5.49  
% 39.43/5.49  fof(f63,plain,(
% 39.43/5.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(nnf_transformation,[],[f35])).
% 39.43/5.49  
% 39.43/5.49  fof(f64,plain,(
% 39.43/5.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(rectify,[],[f63])).
% 39.43/5.49  
% 39.43/5.49  fof(f66,plain,(
% 39.43/5.49    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK6(X0)) != k2_lattices(X0,sK6(X0),X1) & m1_subset_1(sK6(X0),u1_struct_0(X0))))) )),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f65,plain,(
% 39.43/5.49    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK5(X0)) != k2_lattices(X0,sK5(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f67,plain,(
% 39.43/5.49    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f64,f66,f65])).
% 39.43/5.49  
% 39.43/5.49  fof(f102,plain,(
% 39.43/5.49    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f67])).
% 39.43/5.49  
% 39.43/5.49  fof(f116,plain,(
% 39.43/5.49    v10_lattices(sK9)),
% 39.43/5.49    inference(cnf_transformation,[],[f74])).
% 39.43/5.49  
% 39.43/5.49  fof(f117,plain,(
% 39.43/5.49    v4_lattice3(sK9)),
% 39.43/5.49    inference(cnf_transformation,[],[f74])).
% 39.43/5.49  
% 39.43/5.49  fof(f3,axiom,(
% 39.43/5.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f17,plain,(
% 39.43/5.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 39.43/5.49    inference(pure_predicate_removal,[],[f3])).
% 39.43/5.49  
% 39.43/5.49  fof(f18,plain,(
% 39.43/5.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 39.43/5.49    inference(pure_predicate_removal,[],[f17])).
% 39.43/5.49  
% 39.43/5.49  fof(f19,plain,(
% 39.43/5.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 39.43/5.49    inference(pure_predicate_removal,[],[f18])).
% 39.43/5.49  
% 39.43/5.49  fof(f21,plain,(
% 39.43/5.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 39.43/5.49    inference(ennf_transformation,[],[f19])).
% 39.43/5.49  
% 39.43/5.49  fof(f22,plain,(
% 39.43/5.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 39.43/5.49    inference(flattening,[],[f21])).
% 39.43/5.49  
% 39.43/5.49  fof(f78,plain,(
% 39.43/5.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f22])).
% 39.43/5.49  
% 39.43/5.49  fof(f79,plain,(
% 39.43/5.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f22])).
% 39.43/5.49  
% 39.43/5.49  fof(f80,plain,(
% 39.43/5.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f22])).
% 39.43/5.49  
% 39.43/5.49  fof(f92,plain,(
% 39.43/5.49    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f53])).
% 39.43/5.49  
% 39.43/5.49  fof(f8,axiom,(
% 39.43/5.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f30,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 39.43/5.49    inference(ennf_transformation,[],[f8])).
% 39.43/5.49  
% 39.43/5.49  fof(f31,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(flattening,[],[f30])).
% 39.43/5.49  
% 39.43/5.49  fof(f54,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(nnf_transformation,[],[f31])).
% 39.43/5.49  
% 39.43/5.49  fof(f55,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(rectify,[],[f54])).
% 39.43/5.49  
% 39.43/5.49  fof(f56,plain,(
% 39.43/5.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 39.43/5.49    introduced(choice_axiom,[])).
% 39.43/5.49  
% 39.43/5.49  fof(f57,plain,(
% 39.43/5.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 39.43/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 39.43/5.49  
% 39.43/5.49  fof(f95,plain,(
% 39.43/5.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f57])).
% 39.43/5.49  
% 39.43/5.49  fof(f98,plain,(
% 39.43/5.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f62])).
% 39.43/5.49  
% 39.43/5.49  fof(f122,plain,(
% 39.43/5.49    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(equality_resolution,[],[f98])).
% 39.43/5.49  
% 39.43/5.49  fof(f2,axiom,(
% 39.43/5.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f20,plain,(
% 39.43/5.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 39.43/5.49    inference(ennf_transformation,[],[f2])).
% 39.43/5.49  
% 39.43/5.49  fof(f76,plain,(
% 39.43/5.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f20])).
% 39.43/5.49  
% 39.43/5.49  fof(f1,axiom,(
% 39.43/5.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 39.43/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.43/5.49  
% 39.43/5.49  fof(f75,plain,(
% 39.43/5.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f1])).
% 39.43/5.49  
% 39.43/5.49  fof(f86,plain,(
% 39.43/5.49    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f48])).
% 39.43/5.49  
% 39.43/5.49  fof(f84,plain,(
% 39.43/5.49    ( ! [X0,X1] : (k5_lattices(X0) = X1 | k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f47])).
% 39.43/5.49  
% 39.43/5.49  fof(f90,plain,(
% 39.43/5.49    ( ! [X4,X0] : (k2_lattices(X0,X4,sK2(X0)) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f53])).
% 39.43/5.49  
% 39.43/5.49  fof(f99,plain,(
% 39.43/5.49    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f62])).
% 39.43/5.49  
% 39.43/5.49  fof(f82,plain,(
% 39.43/5.49    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(cnf_transformation,[],[f47])).
% 39.43/5.49  
% 39.43/5.49  fof(f120,plain,(
% 39.43/5.49    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 39.43/5.49    inference(equality_resolution,[],[f82])).
% 39.43/5.49  
% 39.43/5.49  fof(f119,plain,(
% 39.43/5.49    k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 39.43/5.49    inference(cnf_transformation,[],[f74])).
% 39.43/5.49  
% 39.43/5.49  cnf(c_666,plain,
% 39.43/5.49      ( X0_62 != X1_62 | X2_62 != X1_62 | X2_62 = X0_62 ),
% 39.43/5.49      theory(equality) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2169,plain,
% 39.43/5.49      ( X0_62 != X1_62
% 39.43/5.49      | X0_62 = k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) != X1_62 ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_666]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_33345,plain,
% 39.43/5.49      ( k15_lattice3(X0_61,X0_63) != X0_62
% 39.43/5.49      | k5_lattices(X0_61) != X0_62
% 39.43/5.49      | k5_lattices(X0_61) = k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2169]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_135477,plain,
% 39.43/5.49      ( k15_lattice3(X0_61,X0_63) != k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
% 39.43/5.49      | k5_lattices(X0_61) != k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
% 39.43/5.49      | k5_lattices(X0_61) = k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_33345]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_135481,plain,
% 39.43/5.49      ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
% 39.43/5.49      | k5_lattices(sK9) != k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
% 39.43/5.49      | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_135477]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_22,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0,X1,X2)
% 39.43/5.49      | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
% 39.43/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.43/5.49      | ~ v4_lattice3(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v10_lattices(X0)
% 39.43/5.49      | k15_lattice3(X0,X2) = X1 ),
% 39.43/5.49      inference(cnf_transformation,[],[f101]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_641,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,X0_62,X0_63)
% 39.43/5.49      | ~ r1_lattices(X0_61,X0_62,sK4(X0_61,X0_63,X0_62))
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_22]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_124117,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,sK2(X0_61),X0_63)
% 39.43/5.49      | ~ r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61)))
% 39.43/5.49      | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_641]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_124122,plain,
% 39.43/5.49      ( k15_lattice3(X0_61,X0_63) = sK2(X0_61)
% 39.43/5.49      | r4_lattice3(X0_61,sK2(X0_61),X0_63) != iProver_top
% 39.43/5.49      | r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) != iProver_top
% 39.43/5.49      | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_124117]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_124124,plain,
% 39.43/5.49      ( k15_lattice3(sK9,k1_xboole_0) = sK2(sK9)
% 39.43/5.49      | r4_lattice3(sK9,sK2(sK9),k1_xboole_0) != iProver_top
% 39.43/5.49      | r1_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) != iProver_top
% 39.43/5.49      | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | v4_lattice3(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_124122]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_11,plain,
% 39.43/5.49      ( r1_lattices(X0,X1,X2)
% 39.43/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.43/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.43/5.49      | ~ v8_lattices(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v9_lattices(X0)
% 39.43/5.49      | k2_lattices(X0,X1,X2) != X1 ),
% 39.43/5.49      inference(cnf_transformation,[],[f87]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_652,plain,
% 39.43/5.49      ( r1_lattices(X0_61,X0_62,X1_62)
% 39.43/5.49      | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ v8_lattices(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v9_lattices(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,X1_62) != X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_11]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2173,plain,
% 39.43/5.49      ( r1_lattices(X0_61,sK2(X0_61),X0_62)
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v8_lattices(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v9_lattices(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,sK2(X0_61),X0_62) != sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_652]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_124116,plain,
% 39.43/5.49      ( r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61)))
% 39.43/5.49      | ~ m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v8_lattices(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v9_lattices(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) != sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2173]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_124118,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) != sK2(X0_61)
% 39.43/5.49      | r1_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,sK2(X0_61))) = iProver_top
% 39.43/5.49      | m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v8_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v9_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_124116]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_124120,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) != sK2(sK9)
% 39.43/5.49      | r1_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) = iProver_top
% 39.43/5.49      | m1_subset_1(sK4(sK9,k1_xboole_0,sK2(sK9)),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | v8_lattices(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v9_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_124118]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2363,plain,
% 39.43/5.49      ( X0_62 != X1_62
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) != X1_62
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62 ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_666]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4874,plain,
% 39.43/5.49      ( X0_62 != sK2(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) != sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2363]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_33727,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X1_61),X0_62) != sK2(X1_61)
% 39.43/5.49      | k15_lattice3(X1_61,X0_63) = k2_lattices(X0_61,sK2(X1_61),X0_62)
% 39.43/5.49      | k15_lattice3(X1_61,X0_63) != sK2(X1_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_4874]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_113455,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) != sK2(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) != sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_33727]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_113456,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) != sK2(sK9)
% 39.43/5.49      | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
% 39.43/5.49      | k15_lattice3(sK9,k1_xboole_0) != sK2(sK9) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_113455]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_8228,plain,
% 39.43/5.49      ( X0_62 != X1_62
% 39.43/5.49      | k5_lattices(X0_61) != X1_62
% 39.43/5.49      | k5_lattices(X0_61) = X0_62 ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_666]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_12461,plain,
% 39.43/5.49      ( X0_62 != k5_lattices(X0_61)
% 39.43/5.49      | k5_lattices(X0_61) = X0_62
% 39.43/5.49      | k5_lattices(X0_61) != k5_lattices(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_8228]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_111967,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) != k5_lattices(X0_61)
% 39.43/5.49      | k5_lattices(X0_61) = k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61))
% 39.43/5.49      | k5_lattices(X0_61) != k5_lattices(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_12461]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_111973,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) != k5_lattices(sK9)
% 39.43/5.49      | k5_lattices(sK9) = k2_lattices(sK9,sK2(sK9),k5_lattices(sK9))
% 39.43/5.49      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_111967]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41,negated_conjecture,
% 39.43/5.49      ( l3_lattices(sK9) ),
% 39.43/5.49      inference(cnf_transformation,[],[f118]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_624,negated_conjecture,
% 39.43/5.49      ( l3_lattices(sK9) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_41]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1422,plain,
% 39.43/5.49      ( l3_lattices(sK9) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_10,plain,
% 39.43/5.49      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f85]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_653,plain,
% 39.43/5.49      ( l1_lattices(X0_61) | ~ l3_lattices(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_10]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1393,plain,
% 39.43/5.49      ( l1_lattices(X0_61) = iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2081,plain,
% 39.43/5.49      ( l1_lattices(sK9) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1422,c_1393]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_17,plain,
% 39.43/5.49      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 39.43/5.49      | ~ l1_lattices(X0)
% 39.43/5.49      | ~ v13_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f88]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_646,plain,
% 39.43/5.49      ( m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_17]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1400,plain,
% 39.43/5.49      ( m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_7,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | ~ v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k5_lattices(X1) = X0 ),
% 39.43/5.49      inference(cnf_transformation,[],[f83]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_656,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | m1_subset_1(sK0(X0_61,X0_62),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k5_lattices(X0_61) = X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_7]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1390,plain,
% 39.43/5.49      ( k5_lattices(X0_61) = X0_62
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK0(X0_61,X0_62),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_16,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | ~ v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k2_lattices(X1,sK2(X1),X0) = sK2(X1) ),
% 39.43/5.49      inference(cnf_transformation,[],[f89]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_647,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,sK2(X0_61),X0_62) = sK2(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_16]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1399,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),X0_62) = sK2(X0_61)
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_3009,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),sK0(X0_61,X0_62)) = sK2(X0_61)
% 39.43/5.49      | k5_lattices(X0_61) = X0_62
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1390,c_1399]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_7010,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),sK0(X0_61,sK2(X0_61))) = sK2(X0_61)
% 39.43/5.49      | sK2(X0_61) = k5_lattices(X0_61)
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1400,c_3009]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_7262,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),sK0(sK9,sK2(sK9))) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9)
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_2081,c_7010]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_44,negated_conjecture,
% 39.43/5.49      ( ~ v2_struct_0(sK9) ),
% 39.43/5.49      inference(cnf_transformation,[],[f115]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_7263,plain,
% 39.43/5.49      ( ~ v13_lattices(sK9)
% 39.43/5.49      | v2_struct_0(sK9)
% 39.43/5.49      | k2_lattices(sK9,sK2(sK9),sK0(sK9,sK2(sK9))) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9) ),
% 39.43/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_7262]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_31,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f106]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_633,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_31]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1413,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_14,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1) ),
% 39.43/5.49      inference(cnf_transformation,[],[f91]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_649,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | m1_subset_1(sK1(X0_61,X0_62),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_14]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1397,plain,
% 39.43/5.49      ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK1(X0_61,X0_62),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_30,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | ~ v6_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 39.43/5.49      inference(cnf_transformation,[],[f102]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_634,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v6_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,X1_62) = k2_lattices(X0_61,X1_62,X0_62) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_30]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1412,plain,
% 39.43/5.49      ( k2_lattices(X0_61,X0_62,X1_62) = k2_lattices(X0_61,X1_62,X0_62)
% 39.43/5.49      | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_3707,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,X0_62),X1_62) = k2_lattices(X0_61,X1_62,sK1(X0_61,X0_62))
% 39.43/5.49      | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1397,c_1412]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_12098,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,X0_62),sK1(X0_61,X1_62)) = k2_lattices(X0_61,sK1(X0_61,X1_62),sK1(X0_61,X0_62))
% 39.43/5.49      | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1397,c_3707]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_15917,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,X1_62)) = k2_lattices(X0_61,sK1(X0_61,X1_62),sK1(X0_61,sK1(X0_61,X0_62)))
% 39.43/5.49      | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1397,c_12098]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_22532,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,X1_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X1_62)),sK1(X0_61,sK1(X0_61,X0_62)))
% 39.43/5.49      | m1_subset_1(X1_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1397,c_15917]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_35095,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,X0_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1413,c_22532]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_704,plain,
% 39.43/5.49      ( l1_lattices(X0_61) = iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_40999,plain,
% 39.43/5.49      ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,X0_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_35095,c_704]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41000,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,X0_62))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,X0_62)),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(renaming,[status(thm)],[c_40999]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41013,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X1_63)))) = k2_lattices(X0_61,sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X1_63))),sK1(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63))))
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1413,c_41000]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41281,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK1(sK9,sK1(sK9,k15_lattice3(sK9,X0_63))),sK1(sK9,sK1(sK9,k15_lattice3(sK9,X1_63)))) = k2_lattices(sK9,sK1(sK9,sK1(sK9,k15_lattice3(sK9,X1_63))),sK1(sK9,sK1(sK9,k15_lattice3(sK9,X0_63))))
% 39.43/5.49      | v13_lattices(sK9) = iProver_top
% 39.43/5.49      | v6_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1422,c_41013]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_45,plain,
% 39.43/5.49      ( v2_struct_0(sK9) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_43,negated_conjecture,
% 39.43/5.49      ( v10_lattices(sK9) ),
% 39.43/5.49      inference(cnf_transformation,[],[f116]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_46,plain,
% 39.43/5.49      ( v10_lattices(sK9) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_42,negated_conjecture,
% 39.43/5.49      ( v4_lattice3(sK9) ),
% 39.43/5.49      inference(cnf_transformation,[],[f117]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_47,plain,
% 39.43/5.49      ( v4_lattice3(sK9) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_48,plain,
% 39.43/5.49      ( l3_lattices(sK9) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_137,plain,
% 39.43/5.49      ( l1_lattices(X0) = iProver_top | l3_lattices(X0) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_139,plain,
% 39.43/5.49      ( l1_lattices(sK9) = iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_137]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4,plain,
% 39.43/5.49      ( v6_lattices(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v10_lattices(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f78]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_153,plain,
% 39.43/5.49      ( v6_lattices(X0) = iProver_top
% 39.43/5.49      | l3_lattices(X0) != iProver_top
% 39.43/5.49      | v2_struct_0(X0) = iProver_top
% 39.43/5.49      | v10_lattices(X0) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_155,plain,
% 39.43/5.49      ( v6_lattices(sK9) = iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_153]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_3,plain,
% 39.43/5.49      ( v8_lattices(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v10_lattices(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f79]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_156,plain,
% 39.43/5.49      ( v8_lattices(X0) = iProver_top
% 39.43/5.49      | l3_lattices(X0) != iProver_top
% 39.43/5.49      | v2_struct_0(X0) = iProver_top
% 39.43/5.49      | v10_lattices(X0) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_158,plain,
% 39.43/5.49      ( v8_lattices(sK9) = iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_156]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2,plain,
% 39.43/5.49      ( ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v10_lattices(X0)
% 39.43/5.49      | v9_lattices(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f80]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_159,plain,
% 39.43/5.49      ( l3_lattices(X0) != iProver_top
% 39.43/5.49      | v2_struct_0(X0) = iProver_top
% 39.43/5.49      | v10_lattices(X0) != iProver_top
% 39.43/5.49      | v9_lattices(X0) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_161,plain,
% 39.43/5.49      ( l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top
% 39.43/5.49      | v9_lattices(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_159]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_756,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_758,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) = iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_756]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1991,plain,
% 39.43/5.49      ( ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
% 39.43/5.49      | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_649]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1992,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_1991]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1994,plain,
% 39.43/5.49      ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) = iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) = iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_1992]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_13,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 39.43/5.49      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 39.43/5.49      inference(cnf_transformation,[],[f92]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_650,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,sK1(X0_61,X0_62)) != X0_62
% 39.43/5.49      | k2_lattices(X0_61,sK1(X0_61,X0_62),X0_62) != X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_13]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2108,plain,
% 39.43/5.49      ( ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) != k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_650]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2109,plain,
% 39.43/5.49      ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) != k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_2108]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2111,plain,
% 39.43/5.49      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
% 39.43/5.49      | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
% 39.43/5.49      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) = iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2109]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_19,plain,
% 39.43/5.49      ( r4_lattice3(X0,X1,X2)
% 39.43/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.43/5.49      | r2_hidden(sK3(X0,X1,X2),X2)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f95]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_644,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,X0_62,X0_63)
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | r2_hidden(sK3(X0_61,X0_62,X0_63),X0_63)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_19]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2375,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)
% 39.43/5.49      | ~ m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61))
% 39.43/5.49      | r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_644]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2386,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63) = iProver_top
% 39.43/5.49      | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63) = iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_2375]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2388,plain,
% 39.43/5.49      ( r4_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0) = iProver_top
% 39.43/5.49      | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | r2_hidden(sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0),k1_xboole_0) = iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2386]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_25,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0,X1,X2)
% 39.43/5.49      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 39.43/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.43/5.49      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 39.43/5.49      | ~ v4_lattice3(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v10_lattices(X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f122]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_638,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,X0_62,X0_63)
% 39.43/5.49      | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_25]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_979,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
% 39.43/5.49      | ~ r4_lattice3(X0_61,X0_62,X0_63)
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61) ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_638,c_633]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_980,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,X0_62,X0_63)
% 39.43/5.49      | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61) ),
% 39.43/5.49      inference(renaming,[status(thm)],[c_979]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2374,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)
% 39.43/5.49      | r1_lattices(X0_61,k15_lattice3(X0_61,X1_63),sK1(X0_61,k15_lattice3(X0_61,X0_63)))
% 39.43/5.49      | ~ m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_980]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2390,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63) != iProver_top
% 39.43/5.49      | r1_lattices(X0_61,k15_lattice3(X0_61,X1_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) = iProver_top
% 39.43/5.49      | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X0_63)),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_2374]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2392,plain,
% 39.43/5.49      ( r4_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0) != iProver_top
% 39.43/5.49      | r1_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) = iProver_top
% 39.43/5.49      | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | v4_lattice3(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2390]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_664,plain,( X0_62 = X0_62 ),theory(equality) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2517,plain,
% 39.43/5.49      ( k15_lattice3(X0_61,X0_63) = k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_664]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2522,plain,
% 39.43/5.49      ( k15_lattice3(sK9,k1_xboole_0) = k15_lattice3(sK9,k1_xboole_0) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2517]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1,plain,
% 39.43/5.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f76]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_661,plain,
% 39.43/5.49      ( ~ r2_hidden(X0_62,X0_63) | ~ r1_tarski(X0_63,X0_62) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_1]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4086,plain,
% 39.43/5.49      ( ~ r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63)
% 39.43/5.49      | ~ r1_tarski(X1_63,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_661]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4092,plain,
% 39.43/5.49      ( r2_hidden(sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63),X1_63) != iProver_top
% 39.43/5.49      | r1_tarski(X1_63,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),X1_63)) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_4086]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4094,plain,
% 39.43/5.49      ( r2_hidden(sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0),k1_xboole_0) != iProver_top
% 39.43/5.49      | r1_tarski(k1_xboole_0,sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0)) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_4092]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_0,plain,
% 39.43/5.49      ( r1_tarski(k1_xboole_0,X0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f75]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_662,plain,
% 39.43/5.49      ( r1_tarski(k1_xboole_0,X0_62) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_0]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4163,plain,
% 39.43/5.49      ( r1_tarski(k1_xboole_0,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k1_xboole_0)) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_662]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4166,plain,
% 39.43/5.49      ( r1_tarski(k1_xboole_0,sK3(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k1_xboole_0)) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_4163]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4168,plain,
% 39.43/5.49      ( r1_tarski(k1_xboole_0,sK3(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k1_xboole_0)) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_4166]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_12,plain,
% 39.43/5.49      ( ~ r1_lattices(X0,X1,X2)
% 39.43/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.43/5.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.43/5.49      | ~ v8_lattices(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v9_lattices(X0)
% 39.43/5.49      | k2_lattices(X0,X1,X2) = X1 ),
% 39.43/5.49      inference(cnf_transformation,[],[f86]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_651,plain,
% 39.43/5.49      ( ~ r1_lattices(X0_61,X0_62,X1_62)
% 39.43/5.49      | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ v8_lattices(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v9_lattices(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,X1_62) = X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_12]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_9710,plain,
% 39.43/5.49      ( ~ r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63)))
% 39.43/5.49      | ~ m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X1_63)),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v8_lattices(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v9_lattices(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) = k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_651]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_9716,plain,
% 39.43/5.49      ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) = k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | r1_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) != iProver_top
% 39.43/5.49      | m1_subset_1(k15_lattice3(X0_61,X0_63),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK1(X0_61,k15_lattice3(X0_61,X1_63)),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v8_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v9_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_9710]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_9718,plain,
% 39.43/5.49      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) = k15_lattice3(sK9,k1_xboole_0)
% 39.43/5.49      | r1_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != iProver_top
% 39.43/5.49      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | v8_lattices(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v9_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_9716]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_3702,plain,
% 39.43/5.49      ( k2_lattices(X0_61,X0_62,k15_lattice3(X0_61,X0_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1413,c_1412]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_9514,plain,
% 39.43/5.49      ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | k2_lattices(X0_61,X0_62,k15_lattice3(X0_61,X0_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_3702,c_704]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_9515,plain,
% 39.43/5.49      ( k2_lattices(X0_61,X0_62,k15_lattice3(X0_61,X0_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),X0_62)
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(renaming,[status(thm)],[c_9514]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_9533,plain,
% 39.43/5.49      ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,X0_62)) = k2_lattices(X0_61,sK1(X0_61,X0_62),k15_lattice3(X0_61,X0_63))
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1397,c_9515]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_13791,plain,
% 39.43/5.49      ( m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,X0_62)) = k2_lattices(X0_61,sK1(X0_61,X0_62),k15_lattice3(X0_61,X0_63))
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_9533,c_704]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_13792,plain,
% 39.43/5.49      ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,X0_62)) = k2_lattices(X0_61,sK1(X0_61,X0_62),k15_lattice3(X0_61,X0_63))
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(renaming,[status(thm)],[c_13791]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_13805,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X1_63)) = k2_lattices(X0_61,k15_lattice3(X0_61,X1_63),sK1(X0_61,k15_lattice3(X0_61,X0_63)))
% 39.43/5.49      | v13_lattices(X0_61) = iProver_top
% 39.43/5.49      | v6_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1413,c_13792]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_13910,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0)))
% 39.43/5.49      | v13_lattices(sK9) = iProver_top
% 39.43/5.49      | v6_lattices(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_13805]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2607,plain,
% 39.43/5.49      ( X0_62 != k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k15_lattice3(X0_61,X1_63) = X0_62
% 39.43/5.49      | k15_lattice3(X0_61,X1_63) != k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2363]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_20481,plain,
% 39.43/5.49      ( k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63))) != k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k15_lattice3(X0_61,X2_63) = k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X1_63)))
% 39.43/5.49      | k15_lattice3(X0_61,X2_63) != k15_lattice3(X0_61,X0_63) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2607]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_20495,plain,
% 39.43/5.49      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
% 39.43/5.49      | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0)))
% 39.43/5.49      | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_20481]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_31684,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != X0_62
% 39.43/5.49      | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) = k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) != X0_62 ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2169]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41176,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) != k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63)))
% 39.43/5.49      | k2_lattices(X0_61,sK1(X0_61,k15_lattice3(X0_61,X0_63)),k15_lattice3(X0_61,X0_63)) = k15_lattice3(X0_61,X0_63)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) != k2_lattices(X0_61,k15_lattice3(X0_61,X0_63),sK1(X0_61,k15_lattice3(X0_61,X0_63))) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_31684]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41178,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0)))
% 39.43/5.49      | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0)
% 39.43/5.49      | k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_41176]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41286,plain,
% 39.43/5.49      ( v13_lattices(sK9) = iProver_top ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_41281,c_45,c_46,c_47,c_48,c_139,c_155,c_158,c_161,
% 39.43/5.49                 c_758,c_1994,c_2111,c_2388,c_2392,c_2522,c_4094,c_4168,
% 39.43/5.49                 c_9718,c_13910,c_20495,c_41178]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41288,plain,
% 39.43/5.49      ( v13_lattices(sK9) ),
% 39.43/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_41286]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_43972,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),sK0(sK9,sK2(sK9))) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9) ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_7262,c_44,c_7263,c_41288]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | ~ v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k2_lattices(X1,X0,sK0(X1,X0)) != X0
% 39.43/5.49      | k2_lattices(X1,sK0(X1,X0),X0) != X0
% 39.43/5.49      | k5_lattices(X1) = X0 ),
% 39.43/5.49      inference(cnf_transformation,[],[f84]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_657,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,sK0(X0_61,X0_62)) != X0_62
% 39.43/5.49      | k2_lattices(X0_61,sK0(X0_61,X0_62),X0_62) != X0_62
% 39.43/5.49      | k5_lattices(X0_61) = X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_6]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1389,plain,
% 39.43/5.49      ( k2_lattices(X0_61,X0_62,sK0(X0_61,X0_62)) != X0_62
% 39.43/5.49      | k2_lattices(X0_61,sK0(X0_61,X0_62),X0_62) != X0_62
% 39.43/5.49      | k5_lattices(X0_61) = X0_62
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_43977,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) != sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9)
% 39.43/5.49      | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_43972,c_1389]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_116,plain,
% 39.43/5.49      ( m1_subset_1(sK2(X0),u1_struct_0(X0)) = iProver_top
% 39.43/5.49      | l1_lattices(X0) != iProver_top
% 39.43/5.49      | v13_lattices(X0) != iProver_top
% 39.43/5.49      | v2_struct_0(X0) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_118,plain,
% 39.43/5.49      ( m1_subset_1(sK2(sK9),u1_struct_0(sK9)) = iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_116]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_15,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | ~ v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
% 39.43/5.49      inference(cnf_transformation,[],[f90]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_648,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,sK2(X0_61)) = sK2(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_15]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1398,plain,
% 39.43/5.49      ( k2_lattices(X0_61,X0_62,sK2(X0_61)) = sK2(X0_61)
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2994,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK0(X0_61,X0_62),sK2(X0_61)) = sK2(X0_61)
% 39.43/5.49      | k5_lattices(X0_61) = X0_62
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1390,c_1398]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6576,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK0(X0_61,sK2(X0_61)),sK2(X0_61)) = sK2(X0_61)
% 39.43/5.49      | sK2(X0_61) = k5_lattices(X0_61)
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1400,c_2994]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6994,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9)
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_2081,c_6576]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6731,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9)
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_6576]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_40935,plain,
% 39.43/5.49      ( v13_lattices(sK9) != iProver_top
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9)
% 39.43/5.49      | k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9) ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_6994,c_45,c_48,c_139,c_6731]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_40936,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9)
% 39.43/5.49      | v13_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(renaming,[status(thm)],[c_40935]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_41291,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK0(sK9,sK2(sK9)),sK2(sK9)) = sK2(sK9)
% 39.43/5.49      | sK2(sK9) = k5_lattices(sK9) ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_41286,c_40936]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_44009,plain,
% 39.43/5.49      ( sK2(sK9) = k5_lattices(sK9) ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_43977,c_45,c_46,c_47,c_48,c_118,c_139,c_155,c_158,
% 39.43/5.49                 c_161,c_758,c_1994,c_2111,c_2388,c_2392,c_2522,c_4094,
% 39.43/5.49                 c_4168,c_9718,c_13910,c_20495,c_41178,c_41291]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_44020,plain,
% 39.43/5.49      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_44009,c_1400]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1384,plain,
% 39.43/5.49      ( r1_tarski(k1_xboole_0,X0_62) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1402,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,X0_62,X0_63) = iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | r2_hidden(sK3(X0_61,X0_62,X0_63),X0_63) = iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1385,plain,
% 39.43/5.49      ( r2_hidden(X0_62,X0_63) != iProver_top
% 39.43/5.49      | r1_tarski(X0_63,X0_62) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_3147,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,X0_62,X0_63) = iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | r1_tarski(X0_63,sK3(X0_61,X0_62,X0_63)) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1402,c_1385]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6232,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,X0_62,k1_xboole_0) = iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1384,c_3147]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6348,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,sK2(X0_61),k1_xboole_0) = iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1400,c_6232]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6837,plain,
% 39.43/5.49      ( r4_lattice3(X0_61,sK2(X0_61),k1_xboole_0) = iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_6348,c_704]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_24,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0,X1,X2)
% 39.43/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.43/5.49      | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
% 39.43/5.49      | ~ v4_lattice3(X0)
% 39.43/5.49      | ~ l3_lattices(X0)
% 39.43/5.49      | v2_struct_0(X0)
% 39.43/5.49      | ~ v10_lattices(X0)
% 39.43/5.49      | k15_lattice3(X0,X2) = X1 ),
% 39.43/5.49      inference(cnf_transformation,[],[f99]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_639,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,X0_62,X0_63)
% 39.43/5.49      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | m1_subset_1(sK4(X0_61,X0_63,X0_62),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62 ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_24]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_1407,plain,
% 39.43/5.49      ( k15_lattice3(X0_61,X0_63) = X0_62
% 39.43/5.49      | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(sK4(X0_61,X0_63,X0_62),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4919,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,X0_62)) = sK2(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62
% 39.43/5.49      | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_1407,c_1399]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_22904,plain,
% 39.43/5.49      ( v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62
% 39.43/5.49      | k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,X0_62)) = sK2(X0_61)
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_4919,c_704]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_22905,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,X0_63,X0_62)) = sK2(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = X0_62
% 39.43/5.49      | r4_lattice3(X0_61,X0_62,X0_63) != iProver_top
% 39.43/5.49      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(renaming,[status(thm)],[c_22904]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_22940,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),sK4(X0_61,k1_xboole_0,sK2(X0_61))) = sK2(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,k1_xboole_0) = sK2(X0_61)
% 39.43/5.49      | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(superposition,[status(thm)],[c_6837,c_22905]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_23476,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),sK4(sK9,k1_xboole_0,sK2(sK9))) = sK2(sK9)
% 39.43/5.49      | k15_lattice3(sK9,k1_xboole_0) = sK2(sK9)
% 39.43/5.49      | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | v4_lattice3(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_22940]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_12462,plain,
% 39.43/5.49      ( k5_lattices(X0_61) = k5_lattices(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_664]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_12464,plain,
% 39.43/5.49      ( k5_lattices(sK9) = k5_lattices(sK9) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_12462]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_6473,plain,
% 39.43/5.49      ( r4_lattice3(sK9,sK2(sK9),k1_xboole_0) = iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_6348]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_8,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.43/5.49      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 39.43/5.49      | ~ l1_lattices(X1)
% 39.43/5.49      | ~ v13_lattices(X1)
% 39.43/5.49      | v2_struct_0(X1)
% 39.43/5.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 39.43/5.49      inference(cnf_transformation,[],[f120]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_655,plain,
% 39.43/5.49      ( ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,X0_62,k5_lattices(X0_61)) = k5_lattices(X0_61) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_8]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4595,plain,
% 39.43/5.49      ( ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = k5_lattices(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_655]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4596,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = k5_lattices(X0_61)
% 39.43/5.49      | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_4595]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4598,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) = k5_lattices(sK9)
% 39.43/5.49      | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_4596]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4435,plain,
% 39.43/5.49      ( ~ m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ l1_lattices(X0_61)
% 39.43/5.49      | ~ v13_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_647]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4476,plain,
% 39.43/5.49      ( k2_lattices(X0_61,sK2(X0_61),k5_lattices(X0_61)) = sK2(X0_61)
% 39.43/5.49      | m1_subset_1(k5_lattices(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | l1_lattices(X0_61) != iProver_top
% 39.43/5.49      | v13_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_4435]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_4478,plain,
% 39.43/5.49      ( k2_lattices(sK9,sK2(sK9),k5_lattices(sK9)) = sK2(sK9)
% 39.43/5.49      | m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | l1_lattices(sK9) != iProver_top
% 39.43/5.49      | v13_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_4476]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2172,plain,
% 39.43/5.49      ( ~ r4_lattice3(X0_61,sK2(X0_61),X0_63)
% 39.43/5.49      | m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61))
% 39.43/5.49      | ~ m1_subset_1(sK2(X0_61),u1_struct_0(X0_61))
% 39.43/5.49      | ~ v4_lattice3(X0_61)
% 39.43/5.49      | ~ l3_lattices(X0_61)
% 39.43/5.49      | v2_struct_0(X0_61)
% 39.43/5.49      | ~ v10_lattices(X0_61)
% 39.43/5.49      | k15_lattice3(X0_61,X0_63) = sK2(X0_61) ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_639]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2203,plain,
% 39.43/5.49      ( k15_lattice3(X0_61,X0_63) = sK2(X0_61)
% 39.43/5.49      | r4_lattice3(X0_61,sK2(X0_61),X0_63) != iProver_top
% 39.43/5.49      | m1_subset_1(sK4(X0_61,X0_63,sK2(X0_61)),u1_struct_0(X0_61)) = iProver_top
% 39.43/5.49      | m1_subset_1(sK2(X0_61),u1_struct_0(X0_61)) != iProver_top
% 39.43/5.49      | v4_lattice3(X0_61) != iProver_top
% 39.43/5.49      | l3_lattices(X0_61) != iProver_top
% 39.43/5.49      | v2_struct_0(X0_61) = iProver_top
% 39.43/5.49      | v10_lattices(X0_61) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_2205,plain,
% 39.43/5.49      ( k15_lattice3(sK9,k1_xboole_0) = sK2(sK9)
% 39.43/5.49      | r4_lattice3(sK9,sK2(sK9),k1_xboole_0) != iProver_top
% 39.43/5.49      | m1_subset_1(sK4(sK9,k1_xboole_0,sK2(sK9)),u1_struct_0(sK9)) = iProver_top
% 39.43/5.49      | m1_subset_1(sK2(sK9),u1_struct_0(sK9)) != iProver_top
% 39.43/5.49      | v4_lattice3(sK9) != iProver_top
% 39.43/5.49      | l3_lattices(sK9) != iProver_top
% 39.43/5.49      | v2_struct_0(sK9) = iProver_top
% 39.43/5.49      | v10_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(instantiation,[status(thm)],[c_2203]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_40,negated_conjecture,
% 39.43/5.49      ( ~ v13_lattices(sK9)
% 39.43/5.49      | ~ l3_lattices(sK9)
% 39.43/5.49      | v2_struct_0(sK9)
% 39.43/5.49      | ~ v10_lattices(sK9)
% 39.43/5.49      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 39.43/5.49      inference(cnf_transformation,[],[f119]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_335,negated_conjecture,
% 39.43/5.49      ( ~ v13_lattices(sK9)
% 39.43/5.49      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 39.43/5.49      inference(global_propositional_subsumption,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_40,c_44,c_43,c_41]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_620,negated_conjecture,
% 39.43/5.49      ( ~ v13_lattices(sK9)
% 39.43/5.49      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 39.43/5.49      inference(subtyping,[status(esa)],[c_335]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(c_787,plain,
% 39.43/5.49      ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
% 39.43/5.49      | v13_lattices(sK9) != iProver_top ),
% 39.43/5.49      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 39.43/5.49  
% 39.43/5.49  cnf(contradiction,plain,
% 39.43/5.49      ( $false ),
% 39.43/5.49      inference(minisat,
% 39.43/5.49                [status(thm)],
% 39.43/5.49                [c_135481,c_124124,c_124120,c_113456,c_111973,c_44020,
% 39.43/5.49                 c_41286,c_23476,c_12464,c_6473,c_4598,c_4478,c_2205,
% 39.43/5.49                 c_787,c_161,c_158,c_139,c_118,c_48,c_47,c_46,c_45]) ).
% 39.43/5.49  
% 39.43/5.49  
% 39.43/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.43/5.49  
% 39.43/5.49  ------                               Statistics
% 39.43/5.49  
% 39.43/5.49  ------ Selected
% 39.43/5.49  
% 39.43/5.49  total_time:                             4.757
% 39.43/5.49  
%------------------------------------------------------------------------------

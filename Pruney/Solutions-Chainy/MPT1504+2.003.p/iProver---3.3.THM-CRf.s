%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:09 EST 2020

% Result     : Theorem 31.91s
% Output     : CNFRefutation 31.91s
% Verified   : 
% Statistics : Number of formulae       :  286 (1557 expanded)
%              Number of clauses        :  206 ( 429 expanded)
%              Number of leaves         :   21 ( 401 expanded)
%              Depth                    :   27
%              Number of atoms          : 1324 (7675 expanded)
%              Number of equality atoms :  174 (1318 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),X2)
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
     => k15_lattice3(X0,sK6) != k16_lattice3(X0,a_2_2_lattice3(X0,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK5,X1) != k16_lattice3(sK5,a_2_2_lattice3(sK5,X1))
      & l3_lattices(sK5)
      & v4_lattice3(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6))
    & l3_lattices(sK5)
    & v4_lattice3(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f48,f47])).

fof(f76,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
                & r4_lattice3(X0,sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f75,plain,(
    v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
                  & r2_hidden(sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK2(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f77,plain,(
    k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_645,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_646,plain,
    ( r4_lattice3(sK5,X0,X1)
    | r2_hidden(sK1(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(sK1(sK5,X0,X1),X1)
    | r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_27])).

cnf(c_651,plain,
    ( r4_lattice3(sK5,X0,X1)
    | r2_hidden(sK1(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_3095,plain,
    ( r4_lattice3(sK5,X0_50,X0_51)
    | r2_hidden(sK1(sK5,X0_50,X0_51),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_108380,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
    | r2_hidden(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),sK6)
    | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3095])).

cnf(c_6,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_624,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_625,plain,
    ( r4_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_629,plain,
    ( m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_27])).

cnf(c_630,plain,
    ( r4_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_3096,plain,
    ( r4_lattice3(sK5,X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0_50,X0_51),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_630])).

cnf(c_108381,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
    | m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3096])).

cnf(c_3118,plain,
    ( ~ r4_lattice3(X0_49,X0_50,X0_51)
    | r4_lattice3(X0_49,X1_50,X0_51)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_104932,plain,
    ( ~ r4_lattice3(sK5,X0_50,sK6)
    | r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)),sK6)
    | k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) != X0_50 ),
    inference(instantiation,[status(thm)],[c_3118])).

cnf(c_106888,plain,
    ( r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)),sK6)
    | ~ r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
    | k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) != k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_104932])).

cnf(c_14,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_571,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_572,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_576,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_27])).

cnf(c_3099,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_576])).

cnf(c_97891,plain,
    ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3099])).

cnf(c_3115,plain,
    ( ~ r1_lattices(X0_49,X0_50,X1_50)
    | r1_lattices(X0_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_3112,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_6031,plain,
    ( ~ r1_lattices(X0_49,X0_50,X1_50)
    | r1_lattices(X0_49,X2_50,X1_50)
    | X2_50 != X0_50 ),
    inference(resolution,[status(thm)],[c_3115,c_3112])).

cnf(c_3113,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_4168,plain,
    ( X0_50 != X1_50
    | X1_50 = X0_50 ),
    inference(resolution,[status(thm)],[c_3113,c_3112])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_586,plain,
    ( v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_587,plain,
    ( v2_struct_0(sK5)
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0)) = k16_lattice3(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_591,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0)) = k16_lattice3(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_27])).

cnf(c_3098,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) = k16_lattice3(sK5,X0_51) ),
    inference(subtyping,[status(esa)],[c_591])).

cnf(c_5029,plain,
    ( k16_lattice3(sK5,X0_51) = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) ),
    inference(resolution,[status(thm)],[c_4168,c_3098])).

cnf(c_6082,plain,
    ( r1_lattices(X0_49,k16_lattice3(sK5,X0_51),X0_50)
    | ~ r1_lattices(X0_49,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X0_50) ),
    inference(resolution,[status(thm)],[c_6031,c_5029])).

cnf(c_11,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_365,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_366,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,X1),u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_26,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_370,plain,
    ( ~ m1_subset_1(k15_lattice3(sK5,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
    | ~ r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_27,c_26,c_24])).

cnf(c_371,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_821,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_576,c_371])).

cnf(c_3087,plain,
    ( ~ r4_lattice3(sK5,X0_50,X0_51)
    | r1_lattices(sK5,k15_lattice3(sK5,X0_51),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_821])).

cnf(c_9420,plain,
    ( ~ r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
    | r1_lattices(sK5,k16_lattice3(sK5,X0_51),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_6082,c_3087])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_795,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | sK3(X0,X1,X2) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_796,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | v2_struct_0(sK5)
    | sK3(X0,sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_800,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | sK3(X0,sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_796,c_27])).

cnf(c_3088,plain,
    ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
    | sK3(X0_50,sK5,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_800])).

cnf(c_5025,plain,
    ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
    | X0_50 = sK3(X0_50,sK5,X0_51) ),
    inference(resolution,[status(thm)],[c_4168,c_3088])).

cnf(c_3114,plain,
    ( ~ r3_lattice3(X0_49,X0_50,X0_51)
    | r3_lattice3(X0_49,X1_50,X0_51)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_5157,plain,
    ( r3_lattice3(X0_49,X0_50,X0_51)
    | ~ r3_lattice3(X0_49,sK3(X0_50,sK5,X1_51),X0_51)
    | ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X1_51)) ),
    inference(resolution,[status(thm)],[c_5025,c_3114])).

cnf(c_16,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_532,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_533,plain,
    ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_537,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | r3_lattice3(sK5,sK3(X0,sK5,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_27])).

cnf(c_538,plain,
    ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_3101,plain,
    ( r3_lattice3(sK5,sK3(X0_50,sK5,X0_51),X0_51)
    | ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51)) ),
    inference(subtyping,[status(esa)],[c_538])).

cnf(c_11129,plain,
    ( r3_lattice3(sK5,X0_50,X0_51)
    | ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51)) ),
    inference(resolution,[status(thm)],[c_5157,c_3101])).

cnf(c_11444,plain,
    ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
    | r3_lattice3(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_11129,c_3095])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_687,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_688,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattice3(sK5,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,X2)
    | ~ r3_lattice3(sK5,X0,X2)
    | r1_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_27])).

cnf(c_693,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattice3(sK5,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_692])).

cnf(c_3093,plain,
    ( r1_lattices(sK5,X0_50,X1_50)
    | ~ r3_lattice3(sK5,X0_50,X0_51)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_693])).

cnf(c_11478,plain,
    ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
    | r1_lattices(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X1_50)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_11444,c_3093])).

cnf(c_3116,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X0_52)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_5155,plain,
    ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
    | m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(sK3(X0_50,sK5,X0_51),X0_52) ),
    inference(resolution,[status(thm)],[c_5025,c_3116])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_777,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_778,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_782,plain,
    ( m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
    | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_778,c_27])).

cnf(c_783,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_782])).

cnf(c_3089,plain,
    ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
    | m1_subset_1(sK3(X0_50,sK5,X0_51),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_783])).

cnf(c_9445,plain,
    ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
    | m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_5155,c_3089])).

cnf(c_9634,plain,
    ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_9445,c_3095])).

cnf(c_36618,plain,
    ( ~ m1_subset_1(X1_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ r2_hidden(X1_50,X0_51)
    | r1_lattices(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X1_50)
    | r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11478,c_9634])).

cnf(c_36619,plain,
    ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
    | r1_lattices(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X1_50)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_36618])).

cnf(c_4,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_666,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_667,plain,
    ( r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
    | r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_27])).

cnf(c_672,plain,
    ( r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_671])).

cnf(c_3094,plain,
    ( r4_lattice3(sK5,X0_50,X0_51)
    | ~ r1_lattices(sK5,sK1(sK5,X0_50,X0_51),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_672])).

cnf(c_37241,plain,
    ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_36619,c_3094])).

cnf(c_41294,plain,
    ( r1_lattices(sK5,k16_lattice3(sK5,X0_51),X0_50)
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_9420,c_37241])).

cnf(c_8,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_437,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_438,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
    | ~ r4_lattice3(sK5,X0,X1)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_27,c_26,c_24])).

cnf(c_443,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k15_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_3104,plain,
    ( ~ r4_lattice3(sK5,X0_50,X0_51)
    | ~ r1_lattices(sK5,X0_50,sK2(sK5,X0_51,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_83638,plain,
    ( ~ r4_lattice3(sK5,k16_lattice3(sK5,X0_51),X1_51)
    | ~ r2_hidden(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),X0_51)
    | ~ m1_subset_1(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),u1_struct_0(sK5))
    | ~ m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5))
    | k15_lattice3(sK5,X1_51) = k16_lattice3(sK5,X0_51) ),
    inference(resolution,[status(thm)],[c_41294,c_3104])).

cnf(c_3593,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3099])).

cnf(c_3710,plain,
    ( m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3098,c_3593])).

cnf(c_3711,plain,
    ( m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3710])).

cnf(c_10,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_389,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_390,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r4_lattice3(sK5,X0,X1)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_27,c_26,c_24])).

cnf(c_395,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
    | k15_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_3106,plain,
    ( ~ r4_lattice3(sK5,X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X0_51,X0_50),u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_395])).

cnf(c_13494,plain,
    ( ~ r4_lattice3(sK5,k16_lattice3(sK5,X0_51),X1_51)
    | m1_subset_1(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),u1_struct_0(sK5))
    | ~ m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5))
    | k15_lattice3(sK5,X1_51) = k16_lattice3(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_3106])).

cnf(c_85170,plain,
    ( ~ r4_lattice3(sK5,k16_lattice3(sK5,X0_51),X1_51)
    | ~ r2_hidden(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),X0_51)
    | k15_lattice3(sK5,X1_51) = k16_lattice3(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_83638,c_3711,c_13494])).

cnf(c_19,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_344,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_345,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | ~ r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_27,c_26,c_24])).

cnf(c_350,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_349])).

cnf(c_3107,plain,
    ( ~ r4_lattice3(sK5,X0_50,X0_51)
    | r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_85196,plain,
    ( ~ r4_lattice3(sK5,sK2(sK5,X0_51,k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51))),X1_51)
    | ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51)),X0_51)
    | ~ m1_subset_1(sK2(sK5,X0_51,k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51))),u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_51) = k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51)) ),
    inference(resolution,[status(thm)],[c_85170,c_3107])).

cnf(c_9,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_413,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_414,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
    | ~ r4_lattice3(sK5,X0,X1)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_27,c_26,c_24])).

cnf(c_419,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k15_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_418])).

cnf(c_3105,plain,
    ( ~ r4_lattice3(sK5,X0_50,X0_51)
    | r4_lattice3(sK5,sK2(sK5,X0_51,X0_50),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_419])).

cnf(c_85307,plain,
    ( ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)),X0_51)
    | ~ m1_subset_1(sK2(sK5,X0_51,k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),u1_struct_0(sK5))
    | ~ m1_subset_1(k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)),u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_51) = k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)) ),
    inference(resolution,[status(thm)],[c_85196,c_3105])).

cnf(c_5041,plain,
    ( m1_subset_1(k16_lattice3(sK5,X0_51),X0_52)
    | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X0_52) ),
    inference(resolution,[status(thm)],[c_5029,c_3116])).

cnf(c_7240,plain,
    ( m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_5041,c_3099])).

cnf(c_85322,plain,
    ( ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)),X0_51)
    | k15_lattice3(sK5,X0_51) = k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_85307,c_7240,c_3106])).

cnf(c_85324,plain,
    ( ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)),sK6)
    | k15_lattice3(sK5,sK6) = k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_85322])).

cnf(c_72977,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))) = k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3098])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK4(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_479,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK4(X0,X1,X2) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_480,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | sK4(X0,sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_484,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | sK4(X0,sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_27,c_26,c_24])).

cnf(c_3102,plain,
    ( ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51))
    | sK4(X0_50,sK5,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_5031,plain,
    ( ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51))
    | X0_50 = sK4(X0_50,sK5,X0_51) ),
    inference(resolution,[status(thm)],[c_4168,c_3102])).

cnf(c_5302,plain,
    ( r4_lattice3(X0_49,X0_50,X0_51)
    | ~ r4_lattice3(X0_49,sK4(X0_50,sK5,X1_51),X0_51)
    | ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X1_51)) ),
    inference(resolution,[status(thm)],[c_5031,c_3118])).

cnf(c_20,plain,
    ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_326,plain,
    ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_327,plain,
    ( r4_lattice3(sK5,sK4(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
    | r4_lattice3(sK5,sK4(X0,sK5,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_27,c_26,c_24])).

cnf(c_332,plain,
    ( r4_lattice3(sK5,sK4(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_3108,plain,
    ( r4_lattice3(sK5,sK4(X0_50,sK5,X0_51),X0_51)
    | ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51)) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_12520,plain,
    ( r4_lattice3(sK5,X0_50,X0_51)
    | ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51)) ),
    inference(resolution,[status(thm)],[c_5302,c_3108])).

cnf(c_1,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_735,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_736,plain,
    ( r3_lattice3(sK5,X0,X1)
    | r2_hidden(sK0(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(sK0(sK5,X0,X1),X1)
    | r3_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_27])).

cnf(c_741,plain,
    ( r3_lattice3(sK5,X0,X1)
    | r2_hidden(sK0(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_3091,plain,
    ( r3_lattice3(sK5,X0_50,X0_51)
    | r2_hidden(sK0(sK5,X0_50,X0_51),X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_741])).

cnf(c_12656,plain,
    ( r4_lattice3(sK5,sK0(sK5,X0_50,a_2_2_lattice3(sK5,X0_51)),X0_51)
    | r3_lattice3(sK5,X0_50,a_2_2_lattice3(sK5,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_12520,c_3091])).

cnf(c_7,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_597,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_598,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK5,X2,X0)
    | ~ r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_27])).

cnf(c_603,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_3097,plain,
    ( ~ r4_lattice3(sK5,X0_50,X0_51)
    | r1_lattices(sK5,X1_50,X0_50)
    | ~ r2_hidden(X1_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_603])).

cnf(c_12734,plain,
    ( r1_lattices(sK5,X0_50,sK0(sK5,X1_50,a_2_2_lattice3(sK5,X0_51)))
    | r3_lattice3(sK5,X1_50,a_2_2_lattice3(sK5,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK5))
    | ~ m1_subset_1(sK0(sK5,X1_50,a_2_2_lattice3(sK5,X0_51)),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_12656,c_3097])).

cnf(c_2,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_714,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_715,plain,
    ( r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_719,plain,
    ( m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r3_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_27])).

cnf(c_720,plain,
    ( r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_3092,plain,
    ( r3_lattice3(sK5,X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | m1_subset_1(sK0(sK5,X0_50,X0_51),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_720])).

cnf(c_38006,plain,
    ( r1_lattices(sK5,X0_50,sK0(sK5,X1_50,a_2_2_lattice3(sK5,X0_51)))
    | r3_lattice3(sK5,X1_50,a_2_2_lattice3(sK5,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12734,c_3092])).

cnf(c_0,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_756,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_757,plain,
    ( ~ r1_lattices(sK5,X0,sK0(sK5,X0,X1))
    | r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r3_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,X0,sK0(sK5,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_757,c_27])).

cnf(c_762,plain,
    ( ~ r1_lattices(sK5,X0,sK0(sK5,X0,X1))
    | r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_761])).

cnf(c_3090,plain,
    ( ~ r1_lattices(sK5,X0_50,sK0(sK5,X0_50,X0_51))
    | r3_lattice3(sK5,X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_762])).

cnf(c_38028,plain,
    ( r3_lattice3(sK5,X0_50,a_2_2_lattice3(sK5,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_38006,c_3090])).

cnf(c_12,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_170,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_311,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_25])).

cnf(c_312,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0),X0)
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_27,c_26,c_24])).

cnf(c_3109,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X0_51) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_4724,plain,
    ( r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_3097,c_3109])).

cnf(c_6560,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK5))
    | ~ r2_hidden(X0_50,X0_51)
    | r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4724,c_3099])).

cnf(c_6561,plain,
    ( r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51))
    | ~ r2_hidden(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_6560])).

cnf(c_6647,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
    | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51)
    | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_3094,c_6561])).

cnf(c_3669,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
    | m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3096])).

cnf(c_3583,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3109])).

cnf(c_3594,plain,
    ( r4_lattice3(sK5,X0_50,X0_51) != iProver_top
    | r1_lattices(sK5,X1_50,X0_50) = iProver_top
    | r2_hidden(X1_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3097])).

cnf(c_5689,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51) != iProver_top
    | r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51)) = iProver_top
    | r2_hidden(X0_50,X1_51) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3593,c_3594])).

cnf(c_6503,plain,
    ( r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51)) = iProver_top
    | r2_hidden(X0_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_5689])).

cnf(c_3597,plain,
    ( r4_lattice3(sK5,X0_50,X0_51) = iProver_top
    | r1_lattices(sK5,sK1(sK5,X0_50,X0_51),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3094])).

cnf(c_6627,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51) = iProver_top
    | r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51) != iProver_top
    | m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6503,c_3597])).

cnf(c_6631,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
    | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51)
    | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6627])).

cnf(c_13975,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
    | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6647,c_3099,c_3669,c_6631])).

cnf(c_15,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_550,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_551,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | ~ r3_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_27])).

cnf(c_556,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_3100,plain,
    ( ~ r3_lattice3(sK5,X0_50,X0_51)
    | r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_556])).

cnf(c_14445,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X1_51)
    | ~ r3_lattice3(sK5,sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X1_51),X0_51)
    | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X1_51),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_13975,c_3100])).

cnf(c_38353,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),X1_51)
    | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),X1_51),X0_51)
    | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),X1_51),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_38028,c_14445])).

cnf(c_38355,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
    | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),sK6)
    | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_38353])).

cnf(c_4459,plain,
    ( k16_lattice3(sK5,X0_51) = k16_lattice3(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_3112])).

cnf(c_9769,plain,
    ( k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) = k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4459])).

cnf(c_3779,plain,
    ( X0_50 != X1_50
    | X0_50 = k15_lattice3(sK5,X0_51)
    | k15_lattice3(sK5,X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_3113])).

cnf(c_4102,plain,
    ( X0_50 != k16_lattice3(sK5,X0_51)
    | X0_50 = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) != k16_lattice3(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_3779])).

cnf(c_4458,plain,
    ( k16_lattice3(sK5,X0_51) != k16_lattice3(sK5,X0_51)
    | k16_lattice3(sK5,X0_51) = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) != k16_lattice3(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_4102])).

cnf(c_6772,plain,
    ( k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6))
    | k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) = k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6)))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4458])).

cnf(c_23,negated_conjecture,
    ( k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3110,negated_conjecture,
    ( k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_108380,c_108381,c_106888,c_97891,c_85324,c_72977,c_38355,c_9769,c_6772,c_3110])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.91/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.91/4.50  
% 31.91/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.91/4.50  
% 31.91/4.50  ------  iProver source info
% 31.91/4.50  
% 31.91/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.91/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.91/4.50  git: non_committed_changes: false
% 31.91/4.50  git: last_make_outside_of_git: false
% 31.91/4.50  
% 31.91/4.50  ------ 
% 31.91/4.50  ------ Parsing...
% 31.91/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.91/4.50  
% 31.91/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 31.91/4.50  
% 31.91/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.91/4.50  
% 31.91/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.91/4.50  ------ Proving...
% 31.91/4.50  ------ Problem Properties 
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  clauses                                 24
% 31.91/4.50  conjectures                             1
% 31.91/4.50  EPR                                     0
% 31.91/4.50  Horn                                    18
% 31.91/4.50  unary                                   4
% 31.91/4.50  binary                                  6
% 31.91/4.50  lits                                    65
% 31.91/4.50  lits eq                                 7
% 31.91/4.50  fd_pure                                 0
% 31.91/4.50  fd_pseudo                               0
% 31.91/4.50  fd_cond                                 0
% 31.91/4.50  fd_pseudo_cond                          3
% 31.91/4.50  AC symbols                              0
% 31.91/4.50  
% 31.91/4.50  ------ Input Options Time Limit: Unbounded
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  ------ 
% 31.91/4.50  Current options:
% 31.91/4.50  ------ 
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  ------ Proving...
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  % SZS status Theorem for theBenchmark.p
% 31.91/4.50  
% 31.91/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.91/4.50  
% 31.91/4.50  fof(f2,axiom,(
% 31.91/4.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f12,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.91/4.50    inference(ennf_transformation,[],[f2])).
% 31.91/4.50  
% 31.91/4.50  fof(f13,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f12])).
% 31.91/4.50  
% 31.91/4.50  fof(f30,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(nnf_transformation,[],[f13])).
% 31.91/4.50  
% 31.91/4.50  fof(f31,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(rectify,[],[f30])).
% 31.91/4.50  
% 31.91/4.50  fof(f32,plain,(
% 31.91/4.50    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f33,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 31.91/4.50  
% 31.91/4.50  fof(f56,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f33])).
% 31.91/4.50  
% 31.91/4.50  fof(f8,conjecture,(
% 31.91/4.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f9,negated_conjecture,(
% 31.91/4.50    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 31.91/4.50    inference(negated_conjecture,[],[f8])).
% 31.91/4.50  
% 31.91/4.50  fof(f24,plain,(
% 31.91/4.50    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 31.91/4.50    inference(ennf_transformation,[],[f9])).
% 31.91/4.50  
% 31.91/4.50  fof(f25,plain,(
% 31.91/4.50    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f24])).
% 31.91/4.50  
% 31.91/4.50  fof(f48,plain,(
% 31.91/4.50    ( ! [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) => k15_lattice3(X0,sK6) != k16_lattice3(X0,a_2_2_lattice3(X0,sK6))) )),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f47,plain,(
% 31.91/4.50    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK5,X1) != k16_lattice3(sK5,a_2_2_lattice3(sK5,X1)) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f49,plain,(
% 31.91/4.50    k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 31.91/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f48,f47])).
% 31.91/4.50  
% 31.91/4.50  fof(f76,plain,(
% 31.91/4.50    l3_lattices(sK5)),
% 31.91/4.50    inference(cnf_transformation,[],[f49])).
% 31.91/4.50  
% 31.91/4.50  fof(f73,plain,(
% 31.91/4.50    ~v2_struct_0(sK5)),
% 31.91/4.50    inference(cnf_transformation,[],[f49])).
% 31.91/4.50  
% 31.91/4.50  fof(f55,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f33])).
% 31.91/4.50  
% 31.91/4.50  fof(f5,axiom,(
% 31.91/4.50    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f18,plain,(
% 31.91/4.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.91/4.50    inference(ennf_transformation,[],[f5])).
% 31.91/4.50  
% 31.91/4.50  fof(f19,plain,(
% 31.91/4.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f18])).
% 31.91/4.50  
% 31.91/4.50  fof(f64,plain,(
% 31.91/4.50    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f19])).
% 31.91/4.50  
% 31.91/4.50  fof(f4,axiom,(
% 31.91/4.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f16,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.91/4.50    inference(ennf_transformation,[],[f4])).
% 31.91/4.50  
% 31.91/4.50  fof(f17,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f16])).
% 31.91/4.50  
% 31.91/4.50  fof(f63,plain,(
% 31.91/4.50    ( ! [X0,X1] : (k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f17])).
% 31.91/4.50  
% 31.91/4.50  fof(f3,axiom,(
% 31.91/4.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f14,plain,(
% 31.91/4.50    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.91/4.50    inference(ennf_transformation,[],[f3])).
% 31.91/4.50  
% 31.91/4.50  fof(f15,plain,(
% 31.91/4.50    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f14])).
% 31.91/4.50  
% 31.91/4.50  fof(f34,plain,(
% 31.91/4.50    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(nnf_transformation,[],[f15])).
% 31.91/4.50  
% 31.91/4.50  fof(f35,plain,(
% 31.91/4.50    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f34])).
% 31.91/4.50  
% 31.91/4.50  fof(f36,plain,(
% 31.91/4.50    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(rectify,[],[f35])).
% 31.91/4.50  
% 31.91/4.50  fof(f37,plain,(
% 31.91/4.50    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f38,plain,(
% 31.91/4.50    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 31.91/4.50  
% 31.91/4.50  fof(f59,plain,(
% 31.91/4.50    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f38])).
% 31.91/4.50  
% 31.91/4.50  fof(f78,plain,(
% 31.91/4.50    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(equality_resolution,[],[f59])).
% 31.91/4.50  
% 31.91/4.50  fof(f75,plain,(
% 31.91/4.50    v4_lattice3(sK5)),
% 31.91/4.50    inference(cnf_transformation,[],[f49])).
% 31.91/4.50  
% 31.91/4.50  fof(f74,plain,(
% 31.91/4.50    v10_lattices(sK5)),
% 31.91/4.50    inference(cnf_transformation,[],[f49])).
% 31.91/4.50  
% 31.91/4.50  fof(f6,axiom,(
% 31.91/4.50    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f20,plain,(
% 31.91/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 31.91/4.50    inference(ennf_transformation,[],[f6])).
% 31.91/4.50  
% 31.91/4.50  fof(f21,plain,(
% 31.91/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(flattening,[],[f20])).
% 31.91/4.50  
% 31.91/4.50  fof(f39,plain,(
% 31.91/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(nnf_transformation,[],[f21])).
% 31.91/4.50  
% 31.91/4.50  fof(f40,plain,(
% 31.91/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(rectify,[],[f39])).
% 31.91/4.50  
% 31.91/4.50  fof(f41,plain,(
% 31.91/4.50    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f42,plain,(
% 31.91/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 31.91/4.50  
% 31.91/4.50  fof(f66,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f42])).
% 31.91/4.50  
% 31.91/4.50  fof(f67,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK3(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f42])).
% 31.91/4.50  
% 31.91/4.50  fof(f1,axiom,(
% 31.91/4.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f10,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.91/4.50    inference(ennf_transformation,[],[f1])).
% 31.91/4.50  
% 31.91/4.50  fof(f11,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(flattening,[],[f10])).
% 31.91/4.50  
% 31.91/4.50  fof(f26,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(nnf_transformation,[],[f11])).
% 31.91/4.50  
% 31.91/4.50  fof(f27,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(rectify,[],[f26])).
% 31.91/4.50  
% 31.91/4.50  fof(f28,plain,(
% 31.91/4.50    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f29,plain,(
% 31.91/4.50    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.91/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 31.91/4.50  
% 31.91/4.50  fof(f50,plain,(
% 31.91/4.50    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f29])).
% 31.91/4.50  
% 31.91/4.50  fof(f65,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f42])).
% 31.91/4.50  
% 31.91/4.50  fof(f57,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f33])).
% 31.91/4.50  
% 31.91/4.50  fof(f62,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f38])).
% 31.91/4.50  
% 31.91/4.50  fof(f60,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f38])).
% 31.91/4.50  
% 31.91/4.50  fof(f7,axiom,(
% 31.91/4.50    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 31.91/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.91/4.50  
% 31.91/4.50  fof(f22,plain,(
% 31.91/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 31.91/4.50    inference(ennf_transformation,[],[f7])).
% 31.91/4.50  
% 31.91/4.50  fof(f23,plain,(
% 31.91/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(flattening,[],[f22])).
% 31.91/4.50  
% 31.91/4.50  fof(f43,plain,(
% 31.91/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(nnf_transformation,[],[f23])).
% 31.91/4.50  
% 31.91/4.50  fof(f44,plain,(
% 31.91/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(rectify,[],[f43])).
% 31.91/4.50  
% 31.91/4.50  fof(f45,plain,(
% 31.91/4.50    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK4(X0,X1,X2),X2) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 31.91/4.50    introduced(choice_axiom,[])).
% 31.91/4.50  
% 31.91/4.50  fof(f46,plain,(
% 31.91/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK4(X0,X1,X2),X2) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.91/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 31.91/4.50  
% 31.91/4.50  fof(f72,plain,(
% 31.91/4.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f46])).
% 31.91/4.50  
% 31.91/4.50  fof(f81,plain,(
% 31.91/4.50    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(equality_resolution,[],[f72])).
% 31.91/4.50  
% 31.91/4.50  fof(f61,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f38])).
% 31.91/4.50  
% 31.91/4.50  fof(f70,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f46])).
% 31.91/4.50  
% 31.91/4.50  fof(f71,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK4(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f46])).
% 31.91/4.50  
% 31.91/4.50  fof(f52,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f29])).
% 31.91/4.50  
% 31.91/4.50  fof(f54,plain,(
% 31.91/4.50    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f33])).
% 31.91/4.50  
% 31.91/4.50  fof(f51,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f29])).
% 31.91/4.50  
% 31.91/4.50  fof(f53,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f29])).
% 31.91/4.50  
% 31.91/4.50  fof(f58,plain,(
% 31.91/4.50    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f38])).
% 31.91/4.50  
% 31.91/4.50  fof(f79,plain,(
% 31.91/4.50    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.91/4.50    inference(equality_resolution,[],[f58])).
% 31.91/4.50  
% 31.91/4.50  fof(f68,plain,(
% 31.91/4.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(cnf_transformation,[],[f42])).
% 31.91/4.50  
% 31.91/4.50  fof(f80,plain,(
% 31.91/4.50    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 31.91/4.50    inference(equality_resolution,[],[f68])).
% 31.91/4.50  
% 31.91/4.50  fof(f77,plain,(
% 31.91/4.50    k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),
% 31.91/4.50    inference(cnf_transformation,[],[f49])).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5,plain,
% 31.91/4.50      ( r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(sK1(X0,X1,X2),X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_24,negated_conjecture,
% 31.91/4.50      ( l3_lattices(sK5) ),
% 31.91/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_645,plain,
% 31.91/4.50      ( r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(sK1(X0,X1,X2),X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_646,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(sK1(sK5,X0,X1),X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_645]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_27,negated_conjecture,
% 31.91/4.50      ( ~ v2_struct_0(sK5) ),
% 31.91/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_650,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r2_hidden(sK1(sK5,X0,X1),X1)
% 31.91/4.50      | r4_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_646,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_651,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(sK1(sK5,X0,X1),X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_650]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3095,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r2_hidden(sK1(sK5,X0_50,X0_51),X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_651]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_108380,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
% 31.91/4.50      | r2_hidden(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),sK6)
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3095]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6,plain,
% 31.91/4.50      ( r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_624,plain,
% 31.91/4.50      ( r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_625,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_624]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_629,plain,
% 31.91/4.50      ( m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r4_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_625,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_630,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_629]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3096,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK1(sK5,X0_50,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_630]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_108381,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
% 31.91/4.50      | m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3096]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3118,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0_49,X0_50,X0_51)
% 31.91/4.50      | r4_lattice3(X0_49,X1_50,X0_51)
% 31.91/4.50      | X1_50 != X0_50 ),
% 31.91/4.50      theory(equality) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_104932,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,sK6)
% 31.91/4.50      | r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)),sK6)
% 31.91/4.50      | k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) != X0_50 ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3118]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_106888,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)),sK6)
% 31.91/4.50      | ~ r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
% 31.91/4.50      | k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) != k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_104932]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_14,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f64]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_571,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_572,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_571]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_576,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_572,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3099,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_576]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_97891,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3099]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3115,plain,
% 31.91/4.50      ( ~ r1_lattices(X0_49,X0_50,X1_50)
% 31.91/4.50      | r1_lattices(X0_49,X2_50,X3_50)
% 31.91/4.50      | X2_50 != X0_50
% 31.91/4.50      | X3_50 != X1_50 ),
% 31.91/4.50      theory(equality) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3112,plain,( X0_50 = X0_50 ),theory(equality) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6031,plain,
% 31.91/4.50      ( ~ r1_lattices(X0_49,X0_50,X1_50)
% 31.91/4.50      | r1_lattices(X0_49,X2_50,X1_50)
% 31.91/4.50      | X2_50 != X0_50 ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_3115,c_3112]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3113,plain,
% 31.91/4.50      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 31.91/4.50      theory(equality) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_4168,plain,
% 31.91/4.50      ( X0_50 != X1_50 | X1_50 = X0_50 ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_3113,c_3112]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_13,plain,
% 31.91/4.50      ( v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
% 31.91/4.50      inference(cnf_transformation,[],[f63]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_586,plain,
% 31.91/4.50      ( v2_struct_0(X0)
% 31.91/4.50      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_587,plain,
% 31.91/4.50      ( v2_struct_0(sK5)
% 31.91/4.50      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0)) = k16_lattice3(sK5,X0) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_586]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_591,plain,
% 31.91/4.50      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0)) = k16_lattice3(sK5,X0) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_587,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3098,plain,
% 31.91/4.50      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) = k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_591]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5029,plain,
% 31.91/4.50      ( k16_lattice3(sK5,X0_51) = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_4168,c_3098]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6082,plain,
% 31.91/4.50      ( r1_lattices(X0_49,k16_lattice3(sK5,X0_51),X0_50)
% 31.91/4.50      | ~ r1_lattices(X0_49,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X0_50) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_6031,c_5029]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_11,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f78]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_25,negated_conjecture,
% 31.91/4.50      ( v4_lattice3(sK5) ),
% 31.91/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_365,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_366,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,X1),u1_struct_0(sK5))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_365]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_26,negated_conjecture,
% 31.91/4.50      ( v10_lattices(sK5) ),
% 31.91/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_370,plain,
% 31.91/4.50      ( ~ m1_subset_1(k15_lattice3(sK5,X1),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
% 31.91/4.50      | ~ r4_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_366,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_371,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,X1),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_370]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_821,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r1_lattices(sK5,k15_lattice3(sK5,X1),X0)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(backward_subsumption_resolution,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_576,c_371]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3087,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r1_lattices(sK5,k15_lattice3(sK5,X0_51),X0_50)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_821]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_9420,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | r1_lattices(sK5,k16_lattice3(sK5,X0_51),X0_50)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_6082,c_3087]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_17,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.91/4.50      | v2_struct_0(X1)
% 31.91/4.50      | ~ l3_lattices(X1)
% 31.91/4.50      | sK3(X0,X1,X2) = X0 ),
% 31.91/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_795,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.91/4.50      | v2_struct_0(X1)
% 31.91/4.50      | sK3(X0,X1,X2) = X0
% 31.91/4.50      | sK5 != X1 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_796,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | sK3(X0,sK5,X1) = X0 ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_795]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_800,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) | sK3(X0,sK5,X1) = X0 ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_796,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3088,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | sK3(X0_50,sK5,X0_51) = X0_50 ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_800]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5025,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | X0_50 = sK3(X0_50,sK5,X0_51) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_4168,c_3088]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3114,plain,
% 31.91/4.50      ( ~ r3_lattice3(X0_49,X0_50,X0_51)
% 31.91/4.50      | r3_lattice3(X0_49,X1_50,X0_51)
% 31.91/4.50      | X1_50 != X0_50 ),
% 31.91/4.50      theory(equality) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5157,plain,
% 31.91/4.50      ( r3_lattice3(X0_49,X0_50,X0_51)
% 31.91/4.50      | ~ r3_lattice3(X0_49,sK3(X0_50,sK5,X1_51),X0_51)
% 31.91/4.50      | ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X1_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5025,c_3114]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_16,plain,
% 31.91/4.50      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 31.91/4.50      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_532,plain,
% 31.91/4.50      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 31.91/4.50      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_533,plain,
% 31.91/4.50      ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
% 31.91/4.50      | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_532]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_537,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | r3_lattice3(sK5,sK3(X0,sK5,X1),X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_533,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_538,plain,
% 31.91/4.50      ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
% 31.91/4.50      | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_537]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3101,plain,
% 31.91/4.50      ( r3_lattice3(sK5,sK3(X0_50,sK5,X0_51),X0_51)
% 31.91/4.50      | ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_538]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_11129,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5157,c_3101]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_11444,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | r3_lattice3(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_11129,c_3095]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3,plain,
% 31.91/4.50      ( r1_lattices(X0,X1,X2)
% 31.91/4.50      | ~ r3_lattice3(X0,X1,X3)
% 31.91/4.50      | ~ r2_hidden(X2,X3)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_687,plain,
% 31.91/4.50      ( r1_lattices(X0,X1,X2)
% 31.91/4.50      | ~ r3_lattice3(X0,X1,X3)
% 31.91/4.50      | ~ r2_hidden(X2,X3)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_688,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0,X1)
% 31.91/4.50      | ~ r3_lattice3(sK5,X0,X2)
% 31.91/4.50      | ~ r2_hidden(X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_687]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_692,plain,
% 31.91/4.50      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ r2_hidden(X1,X2)
% 31.91/4.50      | ~ r3_lattice3(sK5,X0,X2)
% 31.91/4.50      | r1_lattices(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_688,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_693,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0,X1)
% 31.91/4.50      | ~ r3_lattice3(sK5,X0,X2)
% 31.91/4.50      | ~ r2_hidden(X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_692]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3093,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0_50,X1_50)
% 31.91/4.50      | ~ r3_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ r2_hidden(X1_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_693]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_11478,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | r1_lattices(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X1_50)
% 31.91/4.50      | ~ r2_hidden(X1_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_11444,c_3093]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3116,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0_50,X0_52)
% 31.91/4.50      | m1_subset_1(X1_50,X0_52)
% 31.91/4.50      | X1_50 != X0_50 ),
% 31.91/4.50      theory(equality) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5155,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | m1_subset_1(X0_50,X0_52)
% 31.91/4.50      | ~ m1_subset_1(sK3(X0_50,sK5,X0_51),X0_52) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5025,c_3116]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_18,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.91/4.50      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 31.91/4.50      | v2_struct_0(X1)
% 31.91/4.50      | ~ l3_lattices(X1) ),
% 31.91/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_777,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 31.91/4.50      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 31.91/4.50      | v2_struct_0(X1)
% 31.91/4.50      | sK5 != X1 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_778,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_777]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_782,plain,
% 31.91/4.50      ( m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
% 31.91/4.50      | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_778,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_783,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_782]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3089,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | m1_subset_1(sK3(X0_50,sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_783]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_9445,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5155,c_3089]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_9634,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_9445,c_3095]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_36618,plain,
% 31.91/4.50      ( ~ m1_subset_1(X1_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ r2_hidden(X1_50,X0_51)
% 31.91/4.50      | r1_lattices(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X1_50)
% 31.91/4.50      | r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_11478,c_9634]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_36619,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | r1_lattices(sK5,sK1(sK5,X0_50,a_2_1_lattice3(sK5,X0_51)),X1_50)
% 31.91/4.50      | ~ r2_hidden(X1_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_36618]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_4,plain,
% 31.91/4.50      ( r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_666,plain,
% 31.91/4.50      ( r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_667,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_666]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_671,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
% 31.91/4.50      | r4_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_667,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_672,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_671]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3094,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ r1_lattices(sK5,sK1(sK5,X0_50,X0_51),X0_50)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_672]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_37241,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_36619,c_3094]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_41294,plain,
% 31.91/4.50      ( r1_lattices(sK5,k16_lattice3(sK5,X0_51),X0_50)
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_9420,c_37241]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_8,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,X2) = X1 ),
% 31.91/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_437,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,X2) = X1
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_438,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5)
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_437]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_442,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
% 31.91/4.50      | ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_438,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_443,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_442]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3104,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ r1_lattices(sK5,X0_50,sK2(sK5,X0_51,X0_50))
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X0_51) = X0_50 ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_443]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_83638,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,k16_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | ~ r2_hidden(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X1_51) = k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_41294,c_3104]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3593,plain,
% 31.91/4.50      ( m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) = iProver_top ),
% 31.91/4.50      inference(predicate_to_equality,[status(thm)],[c_3099]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3710,plain,
% 31.91/4.50      ( m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5)) = iProver_top ),
% 31.91/4.50      inference(superposition,[status(thm)],[c_3098,c_3593]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3711,plain,
% 31.91/4.50      ( m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_3710]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_10,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,X2) = X1 ),
% 31.91/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_389,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,X2) = X1
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_390,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5)
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_389]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_394,plain,
% 31.91/4.50      ( m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_390,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_395,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_394]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3106,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK2(sK5,X0_51,X0_50),u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X0_51) = X0_50 ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_395]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_13494,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,k16_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | m1_subset_1(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X1_51) = k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3106]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_85170,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,k16_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | ~ r2_hidden(sK2(sK5,X1_51,k16_lattice3(sK5,X0_51)),X0_51)
% 31.91/4.50      | k15_lattice3(sK5,X1_51) = k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_83638,c_3711,c_13494]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_19,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f81]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_344,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_345,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(X0,a_2_2_lattice3(sK5,X1))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_344]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_349,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r2_hidden(X0,a_2_2_lattice3(sK5,X1))
% 31.91/4.50      | ~ r4_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_345,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_350,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(X0,a_2_2_lattice3(sK5,X1))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_349]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3107,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_350]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_85196,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,sK2(sK5,X0_51,k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51))),X1_51)
% 31.91/4.50      | ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51)),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK2(sK5,X0_51,k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51))),u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X0_51) = k16_lattice3(sK5,a_2_2_lattice3(sK5,X1_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_85170,c_3107]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_9,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,X2) = X1 ),
% 31.91/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_413,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | k15_lattice3(X0,X2) = X1
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_414,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5)
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_413]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_418,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
% 31.91/4.50      | ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_414,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_419,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X1) = X0 ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_418]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3105,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r4_lattice3(sK5,sK2(sK5,X0_51,X0_50),X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X0_51) = X0_50 ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_419]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_85307,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK2(sK5,X0_51,k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)),u1_struct_0(sK5))
% 31.91/4.50      | k15_lattice3(sK5,X0_51) = k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_85196,c_3105]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5041,plain,
% 31.91/4.50      ( m1_subset_1(k16_lattice3(sK5,X0_51),X0_52)
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X0_52) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5029,c_3116]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_7240,plain,
% 31.91/4.50      ( m1_subset_1(k16_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5041,c_3099]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_85322,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)),X0_51)
% 31.91/4.50      | k15_lattice3(sK5,X0_51) = k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(forward_subsumption_resolution,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_85307,c_7240,c_3106]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_85324,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)),sK6)
% 31.91/4.50      | k15_lattice3(sK5,sK6) = k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_85322]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_72977,plain,
% 31.91/4.50      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))) = k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3098]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_21,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 31.91/4.50      | ~ v10_lattices(X1)
% 31.91/4.50      | ~ v4_lattice3(X1)
% 31.91/4.50      | v2_struct_0(X1)
% 31.91/4.50      | ~ l3_lattices(X1)
% 31.91/4.50      | sK4(X0,X1,X2) = X0 ),
% 31.91/4.50      inference(cnf_transformation,[],[f70]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_479,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 31.91/4.50      | ~ v10_lattices(X1)
% 31.91/4.50      | v2_struct_0(X1)
% 31.91/4.50      | ~ l3_lattices(X1)
% 31.91/4.50      | sK4(X0,X1,X2) = X0
% 31.91/4.50      | sK5 != X1 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_480,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5)
% 31.91/4.50      | sK4(X0,sK5,X1) = X0 ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_479]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_484,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1)) | sK4(X0,sK5,X1) = X0 ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_480,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3102,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | sK4(X0_50,sK5,X0_51) = X0_50 ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_484]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5031,plain,
% 31.91/4.50      ( ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | X0_50 = sK4(X0_50,sK5,X0_51) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_4168,c_3102]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5302,plain,
% 31.91/4.50      ( r4_lattice3(X0_49,X0_50,X0_51)
% 31.91/4.50      | ~ r4_lattice3(X0_49,sK4(X0_50,sK5,X1_51),X0_51)
% 31.91/4.50      | ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X1_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5031,c_3118]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_20,plain,
% 31.91/4.50      ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
% 31.91/4.50      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f71]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_326,plain,
% 31.91/4.50      ( r4_lattice3(X0,sK4(X1,X0,X2),X2)
% 31.91/4.50      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_327,plain,
% 31.91/4.50      ( r4_lattice3(sK5,sK4(X0,sK5,X1),X1)
% 31.91/4.50      | ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_326]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_331,plain,
% 31.91/4.50      ( ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1))
% 31.91/4.50      | r4_lattice3(sK5,sK4(X0,sK5,X1),X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_327,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_332,plain,
% 31.91/4.50      ( r4_lattice3(sK5,sK4(X0,sK5,X1),X1)
% 31.91/4.50      | ~ r2_hidden(X0,a_2_2_lattice3(sK5,X1)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_331]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3108,plain,
% 31.91/4.50      ( r4_lattice3(sK5,sK4(X0_50,sK5,X0_51),X0_51)
% 31.91/4.50      | ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_332]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_12520,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ r2_hidden(X0_50,a_2_2_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_5302,c_3108]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_1,plain,
% 31.91/4.50      ( r3_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_735,plain,
% 31.91/4.50      ( r3_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_1,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_736,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(sK0(sK5,X0,X1),X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_735]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_740,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r2_hidden(sK0(sK5,X0,X1),X1)
% 31.91/4.50      | r3_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_736,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_741,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(sK0(sK5,X0,X1),X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_740]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3091,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r2_hidden(sK0(sK5,X0_50,X0_51),X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_741]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_12656,plain,
% 31.91/4.50      ( r4_lattice3(sK5,sK0(sK5,X0_50,a_2_2_lattice3(sK5,X0_51)),X0_51)
% 31.91/4.50      | r3_lattice3(sK5,X0_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_12520,c_3091]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_7,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r1_lattices(X0,X3,X1)
% 31.91/4.50      | ~ r2_hidden(X3,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_597,plain,
% 31.91/4.50      ( ~ r4_lattice3(X0,X1,X2)
% 31.91/4.50      | r1_lattices(X0,X3,X1)
% 31.91/4.50      | ~ r2_hidden(X3,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_598,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r1_lattices(sK5,X2,X0)
% 31.91/4.50      | ~ r2_hidden(X2,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_597]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_602,plain,
% 31.91/4.50      ( ~ m1_subset_1(X2,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ r2_hidden(X2,X1)
% 31.91/4.50      | r1_lattices(sK5,X2,X0)
% 31.91/4.50      | ~ r4_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_598,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_603,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0,X1)
% 31.91/4.50      | r1_lattices(sK5,X2,X0)
% 31.91/4.50      | ~ r2_hidden(X2,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X2,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_602]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3097,plain,
% 31.91/4.50      ( ~ r4_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r1_lattices(sK5,X1_50,X0_50)
% 31.91/4.50      | ~ r2_hidden(X1_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_603]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_12734,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0_50,sK0(sK5,X1_50,a_2_2_lattice3(sK5,X0_51)))
% 31.91/4.50      | r3_lattice3(sK5,X1_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(sK0(sK5,X1_50,a_2_2_lattice3(sK5,X0_51)),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_12656,c_3097]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_2,plain,
% 31.91/4.50      ( r3_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_714,plain,
% 31.91/4.50      ( r3_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_715,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_714]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_719,plain,
% 31.91/4.50      ( m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r3_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_715,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_720,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_719]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3092,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | m1_subset_1(sK0(sK5,X0_50,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_720]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_38006,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0_50,sK0(sK5,X1_50,a_2_2_lattice3(sK5,X0_51)))
% 31.91/4.50      | r3_lattice3(sK5,X1_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(X1_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(forward_subsumption_resolution,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_12734,c_3092]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_0,plain,
% 31.91/4.50      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 31.91/4.50      | r3_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_756,plain,
% 31.91/4.50      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 31.91/4.50      | r3_lattice3(X0,X1,X2)
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_757,plain,
% 31.91/4.50      ( ~ r1_lattices(sK5,X0,sK0(sK5,X0,X1))
% 31.91/4.50      | r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_756]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_761,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ r1_lattices(sK5,X0,sK0(sK5,X0,X1)) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_757,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_762,plain,
% 31.91/4.50      ( ~ r1_lattices(sK5,X0,sK0(sK5,X0,X1))
% 31.91/4.50      | r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_761]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3090,plain,
% 31.91/4.50      ( ~ r1_lattices(sK5,X0_50,sK0(sK5,X0_50,X0_51))
% 31.91/4.50      | r3_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_762]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_38028,plain,
% 31.91/4.50      ( r3_lattice3(sK5,X0_50,a_2_2_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_38006,c_3090]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_12,plain,
% 31.91/4.50      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f79]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_170,plain,
% 31.91/4.50      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | ~ v4_lattice3(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_12,c_14]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_311,plain,
% 31.91/4.50      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 31.91/4.50      | ~ v10_lattices(X0)
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_170,c_25]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_312,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0),X0)
% 31.91/4.50      | ~ v10_lattices(sK5)
% 31.91/4.50      | v2_struct_0(sK5)
% 31.91/4.50      | ~ l3_lattices(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_311]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_316,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0),X0) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_312,c_27,c_26,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3109,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X0_51) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_316]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_4724,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_3097,c_3109]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6560,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0_50,u1_struct_0(sK5))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51)) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_4724,c_3099]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6561,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ r2_hidden(X0_50,X0_51)
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_6560]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6647,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_3094,c_6561]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3669,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3096]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3583,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X0_51) = iProver_top ),
% 31.91/4.50      inference(predicate_to_equality,[status(thm)],[c_3109]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3594,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,X0_51) != iProver_top
% 31.91/4.50      | r1_lattices(sK5,X1_50,X0_50) = iProver_top
% 31.91/4.50      | r2_hidden(X1_50,X0_51) != iProver_top
% 31.91/4.50      | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top
% 31.91/4.50      | m1_subset_1(X1_50,u1_struct_0(sK5)) != iProver_top ),
% 31.91/4.50      inference(predicate_to_equality,[status(thm)],[c_3097]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_5689,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51) != iProver_top
% 31.91/4.50      | r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51)) = iProver_top
% 31.91/4.50      | r2_hidden(X0_50,X1_51) != iProver_top
% 31.91/4.50      | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top ),
% 31.91/4.50      inference(superposition,[status(thm)],[c_3593,c_3594]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6503,plain,
% 31.91/4.50      ( r1_lattices(sK5,X0_50,k15_lattice3(sK5,X0_51)) = iProver_top
% 31.91/4.50      | r2_hidden(X0_50,X0_51) != iProver_top
% 31.91/4.50      | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top ),
% 31.91/4.50      inference(superposition,[status(thm)],[c_3583,c_5689]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3597,plain,
% 31.91/4.50      ( r4_lattice3(sK5,X0_50,X0_51) = iProver_top
% 31.91/4.50      | r1_lattices(sK5,sK1(sK5,X0_50,X0_51),X0_50) != iProver_top
% 31.91/4.50      | m1_subset_1(X0_50,u1_struct_0(sK5)) != iProver_top ),
% 31.91/4.50      inference(predicate_to_equality,[status(thm)],[c_3094]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6627,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51) = iProver_top
% 31.91/4.50      | r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51) != iProver_top
% 31.91/4.50      | m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5)) != iProver_top
% 31.91/4.50      | m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) != iProver_top ),
% 31.91/4.50      inference(superposition,[status(thm)],[c_6503,c_3597]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6631,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),u1_struct_0(sK5))
% 31.91/4.50      | ~ m1_subset_1(k15_lattice3(sK5,X0_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_6627]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_13975,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_51),X1_51)
% 31.91/4.50      | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,X0_51),X1_51),X0_51) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_6647,c_3099,c_3669,c_6631]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_15,plain,
% 31.91/4.50      ( ~ r3_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | ~ l3_lattices(X0) ),
% 31.91/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_550,plain,
% 31.91/4.50      ( ~ r3_lattice3(X0,X1,X2)
% 31.91/4.50      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 31.91/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.91/4.50      | v2_struct_0(X0)
% 31.91/4.50      | sK5 != X0 ),
% 31.91/4.50      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_551,plain,
% 31.91/4.50      ( ~ r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | v2_struct_0(sK5) ),
% 31.91/4.50      inference(unflattening,[status(thm)],[c_550]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_555,plain,
% 31.91/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 31.91/4.50      | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | ~ r3_lattice3(sK5,X0,X1) ),
% 31.91/4.50      inference(global_propositional_subsumption,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_551,c_27]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_556,plain,
% 31.91/4.50      ( ~ r3_lattice3(sK5,X0,X1)
% 31.91/4.50      | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 31.91/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(renaming,[status(thm)],[c_555]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3100,plain,
% 31.91/4.50      ( ~ r3_lattice3(sK5,X0_50,X0_51)
% 31.91/4.50      | r2_hidden(X0_50,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | ~ m1_subset_1(X0_50,u1_struct_0(sK5)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_556]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_14445,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X1_51)
% 31.91/4.50      | ~ r3_lattice3(sK5,sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X1_51),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)),X1_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_13975,c_3100]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_38353,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),X1_51)
% 31.91/4.50      | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),X1_51),X0_51)
% 31.91/4.50      | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,X0_51))),X1_51),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(resolution,[status(thm)],[c_38028,c_14445]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_38355,plain,
% 31.91/4.50      ( r4_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6)
% 31.91/4.50      | ~ r2_hidden(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),sK6)
% 31.91/4.50      | ~ m1_subset_1(sK1(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))),sK6),u1_struct_0(sK5)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_38353]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_4459,plain,
% 31.91/4.50      ( k16_lattice3(sK5,X0_51) = k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3112]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_9769,plain,
% 31.91/4.50      ( k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) = k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_4459]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3779,plain,
% 31.91/4.50      ( X0_50 != X1_50
% 31.91/4.50      | X0_50 = k15_lattice3(sK5,X0_51)
% 31.91/4.50      | k15_lattice3(sK5,X0_51) != X1_50 ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3113]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_4102,plain,
% 31.91/4.50      ( X0_50 != k16_lattice3(sK5,X0_51)
% 31.91/4.50      | X0_50 = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) != k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_3779]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_4458,plain,
% 31.91/4.50      ( k16_lattice3(sK5,X0_51) != k16_lattice3(sK5,X0_51)
% 31.91/4.50      | k16_lattice3(sK5,X0_51) = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51))
% 31.91/4.50      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_51)) != k16_lattice3(sK5,X0_51) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_4102]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_6772,plain,
% 31.91/4.50      ( k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6))
% 31.91/4.50      | k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) = k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6)))
% 31.91/4.50      | k15_lattice3(sK5,a_2_1_lattice3(sK5,a_2_2_lattice3(sK5,sK6))) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
% 31.91/4.50      inference(instantiation,[status(thm)],[c_4458]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_23,negated_conjecture,
% 31.91/4.50      ( k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
% 31.91/4.50      inference(cnf_transformation,[],[f77]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(c_3110,negated_conjecture,
% 31.91/4.50      ( k15_lattice3(sK5,sK6) != k16_lattice3(sK5,a_2_2_lattice3(sK5,sK6)) ),
% 31.91/4.50      inference(subtyping,[status(esa)],[c_23]) ).
% 31.91/4.50  
% 31.91/4.50  cnf(contradiction,plain,
% 31.91/4.50      ( $false ),
% 31.91/4.50      inference(minisat,
% 31.91/4.50                [status(thm)],
% 31.91/4.50                [c_108380,c_108381,c_106888,c_97891,c_85324,c_72977,
% 31.91/4.50                 c_38355,c_9769,c_6772,c_3110]) ).
% 31.91/4.50  
% 31.91/4.50  
% 31.91/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.91/4.50  
% 31.91/4.50  ------                               Statistics
% 31.91/4.50  
% 31.91/4.50  ------ Selected
% 31.91/4.50  
% 31.91/4.50  total_time:                             3.75
% 31.91/4.50  
%------------------------------------------------------------------------------

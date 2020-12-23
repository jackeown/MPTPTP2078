%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:22 EST 2020

% Result     : Theorem 27.64s
% Output     : CNFRefutation 27.64s
% Verified   : 
% Statistics : Number of formulae       :  289 (136251 expanded)
%              Number of clauses        :  205 (36387 expanded)
%              Number of leaves         :   25 (26679 expanded)
%              Depth                    :   36
%              Number of atoms          : 1209 (932195 expanded)
%              Number of equality atoms :  396 (107044 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f59,plain,
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
   => ( ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
        | ~ l3_lattices(sK6)
        | ~ v13_lattices(sK6)
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
      & l3_lattices(sK6)
      & v4_lattice3(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
      | ~ l3_lattices(sK6)
      | ~ v13_lattices(sK6)
      | ~ v10_lattices(sK6)
      | v2_struct_0(sK6) )
    & l3_lattices(sK6)
    & v4_lattice3(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f59])).

fof(f94,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f79,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X2)
            | ~ r3_lattices(X0,sK5(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK5(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK5(X0,X1,X2),X1)
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f57])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f66,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f74,plain,(
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

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK4(X0)) != k2_lattices(X0,sK4(X0),X1)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK3(X0)) != k2_lattices(X0,sK3(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),sK4(X0)) != k2_lattices(X0,sK4(X0),sK3(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).

fof(f81,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,
    ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
    | ~ l3_lattices(sK6)
    | ~ v13_lattices(sK6)
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = X1
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = X1
      | k2_lattices(X0,sK0(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK0(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,sK2(X0),X4) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_773,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_774,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_778,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_774,c_34])).

cnf(c_2128,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_778])).

cnf(c_2528,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v13_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_10,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_98,plain,
    ( l1_lattices(sK6)
    | ~ l3_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1044,plain,
    ( m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v13_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1040,c_31,c_98])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
    | v13_lattices(sK6) ),
    inference(renaming,[status(thm)],[c_1044])).

cnf(c_2121,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0_57),u1_struct_0(sK6))
    | v13_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_1045])).

cnf(c_2535,plain,
    ( m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,X0_57),u1_struct_0(sK6)) = iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2121])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_32,negated_conjecture,
    ( v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_33,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_34,c_33,c_31])).

cnf(c_2132,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,X0_57)) = X0_57 ),
    inference(subtyping,[status(esa)],[c_535])).

cnf(c_2524,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,X0_57)) = X0_57
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_3386,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,X0_57))) = sK1(sK6,X0_57)
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_2524])).

cnf(c_4591,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)))) = sK1(sK6,k15_lattice3(sK6,X0_60))
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_3386])).

cnf(c_19,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_965,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_966,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_968,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ v13_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_31,c_98])).

cnf(c_2124,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ v13_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_968])).

cnf(c_2532,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2124])).

cnf(c_2743,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6)
    | v13_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2532,c_2524])).

cnf(c_4632,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)))) = sK1(sK6,k15_lattice3(sK6,X0_60))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(superposition,[status(thm)],[c_4591,c_2743])).

cnf(c_59397,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6)
    | m1_subset_1(sK1(sK6,k15_lattice3(sK6,X0_60)),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4632,c_2528])).

cnf(c_2174,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_2176,plain,
    ( m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1060,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
    | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1060])).

cnf(c_1065,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
    | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1061,c_31,c_98])).

cnf(c_2120,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,X0_57,sK1(sK6,X0_57)) != X0_57
    | k2_lattices(sK6,sK1(sK6,X0_57),X0_57) != X0_57 ),
    inference(subtyping,[status(esa)],[c_1065])).

cnf(c_2727,plain,
    ( ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK1(sK6,k15_lattice3(sK6,X0_60))) != k15_lattice3(sK6,X0_60)
    | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,X0_60)) != k15_lattice3(sK6,X0_60) ),
    inference(instantiation,[status(thm)],[c_2120])).

cnf(c_2728,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK1(sK6,k15_lattice3(sK6,X0_60))) != k15_lattice3(sK6,X0_60)
    | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,X0_60)) != k15_lattice3(sK6,X0_60)
    | m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2727])).

cnf(c_2730,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) != k15_lattice3(sK6,k1_xboole_0)
    | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) != k15_lattice3(sK6,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_391,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_28,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_488,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_489,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
    | r2_hidden(sK5(sK6,X0,X1),X0)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_493,plain,
    ( r2_hidden(sK5(sK6,X0,X1),X0)
    | r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_34,c_33,c_31])).

cnf(c_494,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
    | r2_hidden(sK5(sK6,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_603,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
    | sK5(sK6,X0,X1) != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_494])).

cnf(c_604,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0)) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_2129,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) ),
    inference(subtyping,[status(esa)],[c_604])).

cnf(c_2527,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2129])).

cnf(c_12,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_640,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_33])).

cnf(c_641,plain,
    ( ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | v9_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_120,plain,
    ( ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | v9_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_643,plain,
    ( v9_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_34,c_33,c_31,c_120])).

cnf(c_705,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_643])).

cnf(c_706,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v6_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_114,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_117,plain,
    ( v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_710,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_34,c_33,c_31,c_114,c_117])).

cnf(c_711,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_710])).

cnf(c_14,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_657,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_643])).

cnf(c_658,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_lattices(sK6,X0,X1)
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_34,c_33,c_31,c_117])).

cnf(c_663,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_800,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_711,c_663])).

cnf(c_2127,plain,
    ( ~ r3_lattices(sK6,X0_57,X1_57)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK6))
    | k2_lattices(sK6,X0_57,X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_800])).

cnf(c_2529,plain,
    ( k2_lattices(sK6,X0_57,X1_57) = X0_57
    | r3_lattices(sK6,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2127])).

cnf(c_4479,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = k15_lattice3(sK6,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_2529])).

cnf(c_2175,plain,
    ( m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_2753,plain,
    ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_60),X0_57)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
    | k2_lattices(sK6,k15_lattice3(sK6,X0_60),X0_57) = k15_lattice3(sK6,X0_60) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_3074,plain,
    ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,X1_60))
    | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
    | ~ m1_subset_1(k15_lattice3(sK6,X1_60),u1_struct_0(sK6))
    | k2_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,X1_60)) = k15_lattice3(sK6,X0_60) ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_3813,plain,
    ( ~ r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60))
    | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
    | ~ m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6))
    | k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3074])).

cnf(c_14817,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4479,c_2129,c_2128,c_2175,c_3813])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_980,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v6_lattices(sK6)
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(unflattening,[status(thm)],[c_979])).

cnf(c_618,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_33])).

cnf(c_619,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_621,plain,
    ( v6_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_34,c_33,c_31,c_114])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_621])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v2_struct_0(sK6)
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_983,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_980,c_34,c_31,c_98,c_918])).

cnf(c_2125,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK6))
    | k2_lattices(sK6,X1_57,X0_57) = k2_lattices(sK6,X0_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_983])).

cnf(c_2531,plain,
    ( k2_lattices(sK6,X0_57,X1_57) = k2_lattices(sK6,X1_57,X0_57)
    | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_3043,plain,
    ( k2_lattices(sK6,X0_57,k15_lattice3(sK6,X0_60)) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),X0_57)
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_2531])).

cnf(c_4126,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,X1_60)) = k2_lattices(sK6,k15_lattice3(sK6,X1_60),k15_lattice3(sK6,X0_60)) ),
    inference(superposition,[status(thm)],[c_2528,c_3043])).

cnf(c_14825,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14817,c_4126])).

cnf(c_59375,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(superposition,[status(thm)],[c_4632,c_14825])).

cnf(c_60166,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_59375])).

cnf(c_59376,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,X0_60))) = k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(superposition,[status(thm)],[c_4632,c_14817])).

cnf(c_60167,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) = k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_59376])).

cnf(c_60268,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_59397,c_2176,c_2730,c_2743,c_60166,c_60167])).

cnf(c_60317,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_60268,c_2528])).

cnf(c_61182,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6))
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_60317,c_3386])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK2(sK6)) = sK2(sK6) ),
    inference(unflattening,[status(thm)],[c_1018])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK2(sK6)) = sK2(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1019,c_31,c_98])).

cnf(c_2122,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0_57,sK2(sK6)) = sK2(sK6) ),
    inference(subtyping,[status(esa)],[c_1023])).

cnf(c_2534,plain,
    ( k2_lattices(sK6,X0_57,sK2(sK6)) = sK2(sK6)
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_3030,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
    | v13_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_2534])).

cnf(c_91291,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
    inference(superposition,[status(thm)],[c_61182,c_3030])).

cnf(c_2147,plain,
    ( X0_60 != X1_60
    | k15_lattice3(X0_59,X0_60) = k15_lattice3(X0_59,X1_60) ),
    theory(equality)).

cnf(c_2152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_2141,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_2156,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_30,negated_conjecture,
    ( ~ v13_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_203,negated_conjecture,
    ( ~ v13_lattices(sK6)
    | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_34,c_33,c_31])).

cnf(c_2134,negated_conjecture,
    ( ~ v13_lattices(sK6)
    | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_2158,plain,
    ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k5_lattices(X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k5_lattices(X1) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_1133,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK6,X0),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6)
    | k5_lattices(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_1132])).

cnf(c_1137,plain,
    ( m1_subset_1(sK0(sK6,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k5_lattices(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1133,c_31,c_98])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK6,X0),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k5_lattices(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_1137])).

cnf(c_2117,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK6,X0_57),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k5_lattices(sK6) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1138])).

cnf(c_2903,plain,
    ( m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k5_lattices(sK6) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_2904,plain,
    ( k5_lattices(sK6) = sK2(sK6)
    | m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK2(sK6),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2903])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK0(X1,X0)) != X0
    | k2_lattices(X1,sK0(X1,X0),X0) != X0
    | k5_lattices(X1) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,sK0(X1,X0)) != X0
    | k2_lattices(X1,sK0(X1,X0),X0) != X0
    | k5_lattices(X1) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK0(sK6,X0)) != X0
    | k2_lattices(sK6,sK0(sK6,X0),X0) != X0
    | k5_lattices(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK0(sK6,X0)) != X0
    | k2_lattices(sK6,sK0(sK6,X0),X0) != X0
    | k5_lattices(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1157,c_31,c_98])).

cnf(c_2116,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0_57,sK0(sK6,X0_57)) != X0_57
    | k2_lattices(sK6,sK0(sK6,X0_57),X0_57) != X0_57
    | k5_lattices(sK6) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1161])).

cnf(c_3490,plain,
    ( ~ m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,sK0(sK6,sK2(sK6)),sK2(sK6)) != sK2(sK6)
    | k2_lattices(sK6,sK2(sK6),sK0(sK6,sK2(sK6))) != sK2(sK6)
    | k5_lattices(sK6) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2143,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_2825,plain,
    ( X0_57 != X1_57
    | X0_57 = k15_lattice3(sK6,X0_60)
    | k15_lattice3(sK6,X0_60) != X1_57 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_3237,plain,
    ( X0_57 = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | X0_57 != sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_3824,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6)
    | sK2(sK6) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | sK2(sK6) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_2140,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_3825,plain,
    ( sK2(sK6) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_3834,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6)
    | k5_lattices(sK6) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k5_lattices(sK6) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_4999,plain,
    ( ~ m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,sK0(sK6,sK2(sK6)),sK2(sK6)) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_5022,plain,
    ( k2_lattices(sK6,sK0(sK6,sK2(sK6)),sK2(sK6)) = sK2(sK6)
    | m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4999])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,sK2(X1),X0) = sK2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,sK2(X1),X0) = sK2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_998,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,sK2(sK6),X0) = sK2(sK6) ),
    inference(unflattening,[status(thm)],[c_997])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,sK2(sK6),X0) = sK2(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_31,c_98])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,sK2(sK6),X0_57) = sK2(sK6) ),
    inference(subtyping,[status(esa)],[c_1002])).

cnf(c_4998,plain,
    ( ~ m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,sK2(sK6),sK0(sK6,sK2(sK6))) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_5024,plain,
    ( k2_lattices(sK6,sK2(sK6),sK0(sK6,sK2(sK6))) = sK2(sK6)
    | m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4998])).

cnf(c_3232,plain,
    ( X0_57 != X1_57
    | k15_lattice3(sK6,X0_60) != X1_57
    | k15_lattice3(sK6,X0_60) = X0_57 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_3776,plain,
    ( X0_57 != sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = X0_57
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_3232])).

cnf(c_5769,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) != sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_3776])).

cnf(c_5770,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) != sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_5769])).

cnf(c_3241,plain,
    ( X0_57 != k15_lattice3(sK6,X0_60)
    | X0_57 = k15_lattice3(sK6,X1_60)
    | k15_lattice3(sK6,X1_60) != k15_lattice3(sK6,X0_60) ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_8372,plain,
    ( k15_lattice3(sK6,X0_60) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k5_lattices(sK6) = k15_lattice3(sK6,X0_60)
    | k5_lattices(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_8388,plain,
    ( k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k5_lattices(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k5_lattices(sK6) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8372])).

cnf(c_8584,plain,
    ( m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_8585,plain,
    ( m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8584])).

cnf(c_3772,plain,
    ( X0_57 != k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,k1_xboole_0) = X0_57
    | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3232])).

cnf(c_30346,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) != k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60))
    | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3772])).

cnf(c_30349,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) != k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
    | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30346])).

cnf(c_2145,plain,
    ( ~ m1_subset_1(X0_57,X0_58)
    | m1_subset_1(X1_57,X0_58)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_2758,plain,
    ( m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
    | X0_57 != k15_lattice3(sK6,X0_60) ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_52661,plain,
    ( ~ m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | sK2(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
    inference(instantiation,[status(thm)],[c_2758])).

cnf(c_52662,plain,
    ( sK2(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52661])).

cnf(c_60295,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_60268,c_14825])).

cnf(c_4628,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X1_60)))) = sK1(sK6,k15_lattice3(sK6,X1_60)) ),
    inference(superposition,[status(thm)],[c_4591,c_3030])).

cnf(c_60334,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))) ),
    inference(superposition,[status(thm)],[c_60268,c_4628])).

cnf(c_60669,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
    inference(light_normalisation,[status(thm)],[c_60334,c_60268])).

cnf(c_60371,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),k15_lattice3(sK6,X0_60)) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) ),
    inference(superposition,[status(thm)],[c_60268,c_4126])).

cnf(c_60466,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) ),
    inference(light_normalisation,[status(thm)],[c_60371,c_60268])).

cnf(c_60670,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) = sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
    inference(demodulation,[status(thm)],[c_60669,c_60466])).

cnf(c_61017,plain,
    ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) = sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
    inference(instantiation,[status(thm)],[c_60670])).

cnf(c_61528,plain,
    ( v13_lattices(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_61182])).

cnf(c_33550,plain,
    ( k15_lattice3(sK6,X0_60) != X0_57
    | k15_lattice3(sK6,X0_60) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != X0_57 ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_114159,plain,
    ( k15_lattice3(sK6,X0_60) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X1_60))
    | k15_lattice3(sK6,X0_60) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X1_60)) ),
    inference(instantiation,[status(thm)],[c_33550])).

cnf(c_114160,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
    | k15_lattice3(sK6,k1_xboole_0) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
    | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
    inference(instantiation,[status(thm)],[c_114159])).

cnf(c_114377,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_91291,c_2152,c_2156,c_2158,c_2176,c_2730,c_2743,c_2904,c_3490,c_3824,c_3825,c_3834,c_5022,c_5024,c_5770,c_8388,c_8584,c_8585,c_30349,c_52661,c_52662,c_60166,c_60167,c_60295,c_61017,c_61182,c_61528,c_114160])).

cnf(c_114432,plain,
    ( m1_subset_1(sK1(sK6,sK2(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_114377,c_2528])).

cnf(c_115442,plain,
    ( k2_lattices(sK6,sK1(sK6,sK2(sK6)),sK2(sK6)) = sK2(sK6)
    | v13_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_114432,c_2534])).

cnf(c_2840,plain,
    ( ~ m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,sK1(sK6,sK2(sK6)),sK2(sK6)) != sK2(sK6)
    | k2_lattices(sK6,sK2(sK6),sK1(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2120])).

cnf(c_2892,plain,
    ( ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2893,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
    | m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2892])).

cnf(c_2895,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) = sK2(sK6)
    | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2893])).

cnf(c_5767,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) != sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_3776])).

cnf(c_5768,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) != sK2(sK6)
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_5767])).

cnf(c_30341,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) != k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6))
    | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3772])).

cnf(c_30344,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) != k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
    | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30341])).

cnf(c_60296,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_60268,c_14817])).

cnf(c_114157,plain,
    ( k15_lattice3(sK6,X0_60) != k2_lattices(sK6,k15_lattice3(sK6,X1_60),sK2(sK6))
    | k15_lattice3(sK6,X0_60) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
    | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,k15_lattice3(sK6,X1_60),sK2(sK6)) ),
    inference(instantiation,[status(thm)],[c_33550])).

cnf(c_114158,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
    | k15_lattice3(sK6,k1_xboole_0) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
    | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
    inference(instantiation,[status(thm)],[c_114157])).

cnf(c_2533,plain,
    ( k2_lattices(sK6,sK2(sK6),X0_57) = sK2(sK6)
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_115443,plain,
    ( k2_lattices(sK6,sK2(sK6),sK1(sK6,sK2(sK6))) = sK2(sK6)
    | v13_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_114432,c_2533])).

cnf(c_115906,plain,
    ( v13_lattices(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_115442,c_2152,c_2156,c_2158,c_2176,c_2730,c_2743,c_2840,c_2895,c_2904,c_3490,c_3824,c_3825,c_3834,c_5022,c_5024,c_5768,c_8388,c_8584,c_8585,c_30344,c_52661,c_52662,c_60166,c_60167,c_60296,c_114158,c_115443])).

cnf(c_115989,plain,
    ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)))) = sK1(sK6,k15_lattice3(sK6,X0_60)) ),
    inference(superposition,[status(thm)],[c_4591,c_115906])).

cnf(c_119311,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,X0_60))) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_115989,c_14817])).

cnf(c_119939,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_119311])).

cnf(c_119310,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_115989,c_14825])).

cnf(c_119938,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_119310])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_119939,c_119938,c_115906,c_2730,c_2176])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:54:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.64/3.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.64/3.98  
% 27.64/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.64/3.98  
% 27.64/3.98  ------  iProver source info
% 27.64/3.98  
% 27.64/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.64/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.64/3.98  git: non_committed_changes: false
% 27.64/3.98  git: last_make_outside_of_git: false
% 27.64/3.98  
% 27.64/3.98  ------ 
% 27.64/3.98  
% 27.64/3.98  ------ Input Options
% 27.64/3.98  
% 27.64/3.98  --out_options                           all
% 27.64/3.98  --tptp_safe_out                         true
% 27.64/3.98  --problem_path                          ""
% 27.64/3.98  --include_path                          ""
% 27.64/3.98  --clausifier                            res/vclausify_rel
% 27.64/3.98  --clausifier_options                    --mode clausify
% 27.64/3.98  --stdin                                 false
% 27.64/3.98  --stats_out                             all
% 27.64/3.98  
% 27.64/3.98  ------ General Options
% 27.64/3.98  
% 27.64/3.98  --fof                                   false
% 27.64/3.98  --time_out_real                         305.
% 27.64/3.98  --time_out_virtual                      -1.
% 27.64/3.98  --symbol_type_check                     false
% 27.64/3.98  --clausify_out                          false
% 27.64/3.98  --sig_cnt_out                           false
% 27.64/3.98  --trig_cnt_out                          false
% 27.64/3.98  --trig_cnt_out_tolerance                1.
% 27.64/3.98  --trig_cnt_out_sk_spl                   false
% 27.64/3.98  --abstr_cl_out                          false
% 27.64/3.98  
% 27.64/3.98  ------ Global Options
% 27.64/3.98  
% 27.64/3.98  --schedule                              default
% 27.64/3.98  --add_important_lit                     false
% 27.64/3.98  --prop_solver_per_cl                    1000
% 27.64/3.98  --min_unsat_core                        false
% 27.64/3.98  --soft_assumptions                      false
% 27.64/3.98  --soft_lemma_size                       3
% 27.64/3.98  --prop_impl_unit_size                   0
% 27.64/3.98  --prop_impl_unit                        []
% 27.64/3.98  --share_sel_clauses                     true
% 27.64/3.98  --reset_solvers                         false
% 27.64/3.98  --bc_imp_inh                            [conj_cone]
% 27.64/3.98  --conj_cone_tolerance                   3.
% 27.64/3.98  --extra_neg_conj                        none
% 27.64/3.98  --large_theory_mode                     true
% 27.64/3.98  --prolific_symb_bound                   200
% 27.64/3.98  --lt_threshold                          2000
% 27.64/3.98  --clause_weak_htbl                      true
% 27.64/3.98  --gc_record_bc_elim                     false
% 27.64/3.98  
% 27.64/3.98  ------ Preprocessing Options
% 27.64/3.98  
% 27.64/3.98  --preprocessing_flag                    true
% 27.64/3.98  --time_out_prep_mult                    0.1
% 27.64/3.98  --splitting_mode                        input
% 27.64/3.98  --splitting_grd                         true
% 27.64/3.98  --splitting_cvd                         false
% 27.64/3.98  --splitting_cvd_svl                     false
% 27.64/3.98  --splitting_nvd                         32
% 27.64/3.98  --sub_typing                            true
% 27.64/3.98  --prep_gs_sim                           true
% 27.64/3.98  --prep_unflatten                        true
% 27.64/3.98  --prep_res_sim                          true
% 27.64/3.98  --prep_upred                            true
% 27.64/3.98  --prep_sem_filter                       exhaustive
% 27.64/3.98  --prep_sem_filter_out                   false
% 27.64/3.98  --pred_elim                             true
% 27.64/3.98  --res_sim_input                         true
% 27.64/3.98  --eq_ax_congr_red                       true
% 27.64/3.98  --pure_diseq_elim                       true
% 27.64/3.98  --brand_transform                       false
% 27.64/3.98  --non_eq_to_eq                          false
% 27.64/3.98  --prep_def_merge                        true
% 27.64/3.98  --prep_def_merge_prop_impl              false
% 27.64/3.98  --prep_def_merge_mbd                    true
% 27.64/3.98  --prep_def_merge_tr_red                 false
% 27.64/3.98  --prep_def_merge_tr_cl                  false
% 27.64/3.98  --smt_preprocessing                     true
% 27.64/3.98  --smt_ac_axioms                         fast
% 27.64/3.98  --preprocessed_out                      false
% 27.64/3.98  --preprocessed_stats                    false
% 27.64/3.98  
% 27.64/3.98  ------ Abstraction refinement Options
% 27.64/3.98  
% 27.64/3.98  --abstr_ref                             []
% 27.64/3.98  --abstr_ref_prep                        false
% 27.64/3.98  --abstr_ref_until_sat                   false
% 27.64/3.98  --abstr_ref_sig_restrict                funpre
% 27.64/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.64/3.98  --abstr_ref_under                       []
% 27.64/3.98  
% 27.64/3.98  ------ SAT Options
% 27.64/3.98  
% 27.64/3.98  --sat_mode                              false
% 27.64/3.98  --sat_fm_restart_options                ""
% 27.64/3.98  --sat_gr_def                            false
% 27.64/3.98  --sat_epr_types                         true
% 27.64/3.98  --sat_non_cyclic_types                  false
% 27.64/3.98  --sat_finite_models                     false
% 27.64/3.98  --sat_fm_lemmas                         false
% 27.64/3.98  --sat_fm_prep                           false
% 27.64/3.98  --sat_fm_uc_incr                        true
% 27.64/3.98  --sat_out_model                         small
% 27.64/3.98  --sat_out_clauses                       false
% 27.64/3.98  
% 27.64/3.98  ------ QBF Options
% 27.64/3.98  
% 27.64/3.98  --qbf_mode                              false
% 27.64/3.98  --qbf_elim_univ                         false
% 27.64/3.98  --qbf_dom_inst                          none
% 27.64/3.98  --qbf_dom_pre_inst                      false
% 27.64/3.98  --qbf_sk_in                             false
% 27.64/3.98  --qbf_pred_elim                         true
% 27.64/3.98  --qbf_split                             512
% 27.64/3.98  
% 27.64/3.98  ------ BMC1 Options
% 27.64/3.98  
% 27.64/3.98  --bmc1_incremental                      false
% 27.64/3.98  --bmc1_axioms                           reachable_all
% 27.64/3.98  --bmc1_min_bound                        0
% 27.64/3.98  --bmc1_max_bound                        -1
% 27.64/3.98  --bmc1_max_bound_default                -1
% 27.64/3.98  --bmc1_symbol_reachability              true
% 27.64/3.98  --bmc1_property_lemmas                  false
% 27.64/3.98  --bmc1_k_induction                      false
% 27.64/3.98  --bmc1_non_equiv_states                 false
% 27.64/3.98  --bmc1_deadlock                         false
% 27.64/3.98  --bmc1_ucm                              false
% 27.64/3.98  --bmc1_add_unsat_core                   none
% 27.64/3.98  --bmc1_unsat_core_children              false
% 27.64/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.64/3.98  --bmc1_out_stat                         full
% 27.64/3.98  --bmc1_ground_init                      false
% 27.64/3.98  --bmc1_pre_inst_next_state              false
% 27.64/3.98  --bmc1_pre_inst_state                   false
% 27.64/3.98  --bmc1_pre_inst_reach_state             false
% 27.64/3.98  --bmc1_out_unsat_core                   false
% 27.64/3.98  --bmc1_aig_witness_out                  false
% 27.64/3.98  --bmc1_verbose                          false
% 27.64/3.98  --bmc1_dump_clauses_tptp                false
% 27.64/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.64/3.98  --bmc1_dump_file                        -
% 27.64/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.64/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.64/3.98  --bmc1_ucm_extend_mode                  1
% 27.64/3.98  --bmc1_ucm_init_mode                    2
% 27.64/3.98  --bmc1_ucm_cone_mode                    none
% 27.64/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.64/3.98  --bmc1_ucm_relax_model                  4
% 27.64/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.64/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.64/3.98  --bmc1_ucm_layered_model                none
% 27.64/3.98  --bmc1_ucm_max_lemma_size               10
% 27.64/3.98  
% 27.64/3.98  ------ AIG Options
% 27.64/3.98  
% 27.64/3.98  --aig_mode                              false
% 27.64/3.98  
% 27.64/3.98  ------ Instantiation Options
% 27.64/3.98  
% 27.64/3.98  --instantiation_flag                    true
% 27.64/3.98  --inst_sos_flag                         false
% 27.64/3.98  --inst_sos_phase                        true
% 27.64/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.64/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.64/3.98  --inst_lit_sel_side                     num_symb
% 27.64/3.98  --inst_solver_per_active                1400
% 27.64/3.98  --inst_solver_calls_frac                1.
% 27.64/3.98  --inst_passive_queue_type               priority_queues
% 27.64/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.64/3.98  --inst_passive_queues_freq              [25;2]
% 27.64/3.98  --inst_dismatching                      true
% 27.64/3.98  --inst_eager_unprocessed_to_passive     true
% 27.64/3.98  --inst_prop_sim_given                   true
% 27.64/3.98  --inst_prop_sim_new                     false
% 27.64/3.98  --inst_subs_new                         false
% 27.64/3.98  --inst_eq_res_simp                      false
% 27.64/3.98  --inst_subs_given                       false
% 27.64/3.98  --inst_orphan_elimination               true
% 27.64/3.98  --inst_learning_loop_flag               true
% 27.64/3.98  --inst_learning_start                   3000
% 27.64/3.98  --inst_learning_factor                  2
% 27.64/3.98  --inst_start_prop_sim_after_learn       3
% 27.64/3.98  --inst_sel_renew                        solver
% 27.64/3.98  --inst_lit_activity_flag                true
% 27.64/3.98  --inst_restr_to_given                   false
% 27.64/3.98  --inst_activity_threshold               500
% 27.64/3.98  --inst_out_proof                        true
% 27.64/3.98  
% 27.64/3.98  ------ Resolution Options
% 27.64/3.98  
% 27.64/3.98  --resolution_flag                       true
% 27.64/3.98  --res_lit_sel                           adaptive
% 27.64/3.98  --res_lit_sel_side                      none
% 27.64/3.98  --res_ordering                          kbo
% 27.64/3.98  --res_to_prop_solver                    active
% 27.64/3.98  --res_prop_simpl_new                    false
% 27.64/3.98  --res_prop_simpl_given                  true
% 27.64/3.98  --res_passive_queue_type                priority_queues
% 27.64/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.64/3.98  --res_passive_queues_freq               [15;5]
% 27.64/3.98  --res_forward_subs                      full
% 27.64/3.98  --res_backward_subs                     full
% 27.64/3.98  --res_forward_subs_resolution           true
% 27.64/3.98  --res_backward_subs_resolution          true
% 27.64/3.98  --res_orphan_elimination                true
% 27.64/3.98  --res_time_limit                        2.
% 27.64/3.98  --res_out_proof                         true
% 27.64/3.98  
% 27.64/3.98  ------ Superposition Options
% 27.64/3.98  
% 27.64/3.98  --superposition_flag                    true
% 27.64/3.98  --sup_passive_queue_type                priority_queues
% 27.64/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.64/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.64/3.98  --demod_completeness_check              fast
% 27.64/3.98  --demod_use_ground                      true
% 27.64/3.98  --sup_to_prop_solver                    passive
% 27.64/3.98  --sup_prop_simpl_new                    true
% 27.64/3.98  --sup_prop_simpl_given                  true
% 27.64/3.98  --sup_fun_splitting                     false
% 27.64/3.98  --sup_smt_interval                      50000
% 27.64/3.99  
% 27.64/3.99  ------ Superposition Simplification Setup
% 27.64/3.99  
% 27.64/3.99  --sup_indices_passive                   []
% 27.64/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.64/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.64/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.64/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.64/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.64/3.99  --sup_full_bw                           [BwDemod]
% 27.64/3.99  --sup_immed_triv                        [TrivRules]
% 27.64/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.64/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.64/3.99  --sup_immed_bw_main                     []
% 27.64/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.64/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.64/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.64/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.64/3.99  
% 27.64/3.99  ------ Combination Options
% 27.64/3.99  
% 27.64/3.99  --comb_res_mult                         3
% 27.64/3.99  --comb_sup_mult                         2
% 27.64/3.99  --comb_inst_mult                        10
% 27.64/3.99  
% 27.64/3.99  ------ Debug Options
% 27.64/3.99  
% 27.64/3.99  --dbg_backtrace                         false
% 27.64/3.99  --dbg_dump_prop_clauses                 false
% 27.64/3.99  --dbg_dump_prop_clauses_file            -
% 27.64/3.99  --dbg_out_stat                          false
% 27.64/3.99  ------ Parsing...
% 27.64/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.64/3.99  
% 27.64/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 27.64/3.99  
% 27.64/3.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.64/3.99  
% 27.64/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.64/3.99  ------ Proving...
% 27.64/3.99  ------ Problem Properties 
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  clauses                                 21
% 27.64/3.99  conjectures                             1
% 27.64/3.99  EPR                                     0
% 27.64/3.99  Horn                                    17
% 27.64/3.99  unary                                   2
% 27.64/3.99  binary                                  5
% 27.64/3.99  lits                                    60
% 27.64/3.99  lits eq                                 16
% 27.64/3.99  fd_pure                                 0
% 27.64/3.99  fd_pseudo                               0
% 27.64/3.99  fd_cond                                 2
% 27.64/3.99  fd_pseudo_cond                          0
% 27.64/3.99  AC symbols                              0
% 27.64/3.99  
% 27.64/3.99  ------ Schedule dynamic 5 is on 
% 27.64/3.99  
% 27.64/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  ------ 
% 27.64/3.99  Current options:
% 27.64/3.99  ------ 
% 27.64/3.99  
% 27.64/3.99  ------ Input Options
% 27.64/3.99  
% 27.64/3.99  --out_options                           all
% 27.64/3.99  --tptp_safe_out                         true
% 27.64/3.99  --problem_path                          ""
% 27.64/3.99  --include_path                          ""
% 27.64/3.99  --clausifier                            res/vclausify_rel
% 27.64/3.99  --clausifier_options                    --mode clausify
% 27.64/3.99  --stdin                                 false
% 27.64/3.99  --stats_out                             all
% 27.64/3.99  
% 27.64/3.99  ------ General Options
% 27.64/3.99  
% 27.64/3.99  --fof                                   false
% 27.64/3.99  --time_out_real                         305.
% 27.64/3.99  --time_out_virtual                      -1.
% 27.64/3.99  --symbol_type_check                     false
% 27.64/3.99  --clausify_out                          false
% 27.64/3.99  --sig_cnt_out                           false
% 27.64/3.99  --trig_cnt_out                          false
% 27.64/3.99  --trig_cnt_out_tolerance                1.
% 27.64/3.99  --trig_cnt_out_sk_spl                   false
% 27.64/3.99  --abstr_cl_out                          false
% 27.64/3.99  
% 27.64/3.99  ------ Global Options
% 27.64/3.99  
% 27.64/3.99  --schedule                              default
% 27.64/3.99  --add_important_lit                     false
% 27.64/3.99  --prop_solver_per_cl                    1000
% 27.64/3.99  --min_unsat_core                        false
% 27.64/3.99  --soft_assumptions                      false
% 27.64/3.99  --soft_lemma_size                       3
% 27.64/3.99  --prop_impl_unit_size                   0
% 27.64/3.99  --prop_impl_unit                        []
% 27.64/3.99  --share_sel_clauses                     true
% 27.64/3.99  --reset_solvers                         false
% 27.64/3.99  --bc_imp_inh                            [conj_cone]
% 27.64/3.99  --conj_cone_tolerance                   3.
% 27.64/3.99  --extra_neg_conj                        none
% 27.64/3.99  --large_theory_mode                     true
% 27.64/3.99  --prolific_symb_bound                   200
% 27.64/3.99  --lt_threshold                          2000
% 27.64/3.99  --clause_weak_htbl                      true
% 27.64/3.99  --gc_record_bc_elim                     false
% 27.64/3.99  
% 27.64/3.99  ------ Preprocessing Options
% 27.64/3.99  
% 27.64/3.99  --preprocessing_flag                    true
% 27.64/3.99  --time_out_prep_mult                    0.1
% 27.64/3.99  --splitting_mode                        input
% 27.64/3.99  --splitting_grd                         true
% 27.64/3.99  --splitting_cvd                         false
% 27.64/3.99  --splitting_cvd_svl                     false
% 27.64/3.99  --splitting_nvd                         32
% 27.64/3.99  --sub_typing                            true
% 27.64/3.99  --prep_gs_sim                           true
% 27.64/3.99  --prep_unflatten                        true
% 27.64/3.99  --prep_res_sim                          true
% 27.64/3.99  --prep_upred                            true
% 27.64/3.99  --prep_sem_filter                       exhaustive
% 27.64/3.99  --prep_sem_filter_out                   false
% 27.64/3.99  --pred_elim                             true
% 27.64/3.99  --res_sim_input                         true
% 27.64/3.99  --eq_ax_congr_red                       true
% 27.64/3.99  --pure_diseq_elim                       true
% 27.64/3.99  --brand_transform                       false
% 27.64/3.99  --non_eq_to_eq                          false
% 27.64/3.99  --prep_def_merge                        true
% 27.64/3.99  --prep_def_merge_prop_impl              false
% 27.64/3.99  --prep_def_merge_mbd                    true
% 27.64/3.99  --prep_def_merge_tr_red                 false
% 27.64/3.99  --prep_def_merge_tr_cl                  false
% 27.64/3.99  --smt_preprocessing                     true
% 27.64/3.99  --smt_ac_axioms                         fast
% 27.64/3.99  --preprocessed_out                      false
% 27.64/3.99  --preprocessed_stats                    false
% 27.64/3.99  
% 27.64/3.99  ------ Abstraction refinement Options
% 27.64/3.99  
% 27.64/3.99  --abstr_ref                             []
% 27.64/3.99  --abstr_ref_prep                        false
% 27.64/3.99  --abstr_ref_until_sat                   false
% 27.64/3.99  --abstr_ref_sig_restrict                funpre
% 27.64/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.64/3.99  --abstr_ref_under                       []
% 27.64/3.99  
% 27.64/3.99  ------ SAT Options
% 27.64/3.99  
% 27.64/3.99  --sat_mode                              false
% 27.64/3.99  --sat_fm_restart_options                ""
% 27.64/3.99  --sat_gr_def                            false
% 27.64/3.99  --sat_epr_types                         true
% 27.64/3.99  --sat_non_cyclic_types                  false
% 27.64/3.99  --sat_finite_models                     false
% 27.64/3.99  --sat_fm_lemmas                         false
% 27.64/3.99  --sat_fm_prep                           false
% 27.64/3.99  --sat_fm_uc_incr                        true
% 27.64/3.99  --sat_out_model                         small
% 27.64/3.99  --sat_out_clauses                       false
% 27.64/3.99  
% 27.64/3.99  ------ QBF Options
% 27.64/3.99  
% 27.64/3.99  --qbf_mode                              false
% 27.64/3.99  --qbf_elim_univ                         false
% 27.64/3.99  --qbf_dom_inst                          none
% 27.64/3.99  --qbf_dom_pre_inst                      false
% 27.64/3.99  --qbf_sk_in                             false
% 27.64/3.99  --qbf_pred_elim                         true
% 27.64/3.99  --qbf_split                             512
% 27.64/3.99  
% 27.64/3.99  ------ BMC1 Options
% 27.64/3.99  
% 27.64/3.99  --bmc1_incremental                      false
% 27.64/3.99  --bmc1_axioms                           reachable_all
% 27.64/3.99  --bmc1_min_bound                        0
% 27.64/3.99  --bmc1_max_bound                        -1
% 27.64/3.99  --bmc1_max_bound_default                -1
% 27.64/3.99  --bmc1_symbol_reachability              true
% 27.64/3.99  --bmc1_property_lemmas                  false
% 27.64/3.99  --bmc1_k_induction                      false
% 27.64/3.99  --bmc1_non_equiv_states                 false
% 27.64/3.99  --bmc1_deadlock                         false
% 27.64/3.99  --bmc1_ucm                              false
% 27.64/3.99  --bmc1_add_unsat_core                   none
% 27.64/3.99  --bmc1_unsat_core_children              false
% 27.64/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.64/3.99  --bmc1_out_stat                         full
% 27.64/3.99  --bmc1_ground_init                      false
% 27.64/3.99  --bmc1_pre_inst_next_state              false
% 27.64/3.99  --bmc1_pre_inst_state                   false
% 27.64/3.99  --bmc1_pre_inst_reach_state             false
% 27.64/3.99  --bmc1_out_unsat_core                   false
% 27.64/3.99  --bmc1_aig_witness_out                  false
% 27.64/3.99  --bmc1_verbose                          false
% 27.64/3.99  --bmc1_dump_clauses_tptp                false
% 27.64/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.64/3.99  --bmc1_dump_file                        -
% 27.64/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.64/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.64/3.99  --bmc1_ucm_extend_mode                  1
% 27.64/3.99  --bmc1_ucm_init_mode                    2
% 27.64/3.99  --bmc1_ucm_cone_mode                    none
% 27.64/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.64/3.99  --bmc1_ucm_relax_model                  4
% 27.64/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.64/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.64/3.99  --bmc1_ucm_layered_model                none
% 27.64/3.99  --bmc1_ucm_max_lemma_size               10
% 27.64/3.99  
% 27.64/3.99  ------ AIG Options
% 27.64/3.99  
% 27.64/3.99  --aig_mode                              false
% 27.64/3.99  
% 27.64/3.99  ------ Instantiation Options
% 27.64/3.99  
% 27.64/3.99  --instantiation_flag                    true
% 27.64/3.99  --inst_sos_flag                         false
% 27.64/3.99  --inst_sos_phase                        true
% 27.64/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.64/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.64/3.99  --inst_lit_sel_side                     none
% 27.64/3.99  --inst_solver_per_active                1400
% 27.64/3.99  --inst_solver_calls_frac                1.
% 27.64/3.99  --inst_passive_queue_type               priority_queues
% 27.64/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.64/3.99  --inst_passive_queues_freq              [25;2]
% 27.64/3.99  --inst_dismatching                      true
% 27.64/3.99  --inst_eager_unprocessed_to_passive     true
% 27.64/3.99  --inst_prop_sim_given                   true
% 27.64/3.99  --inst_prop_sim_new                     false
% 27.64/3.99  --inst_subs_new                         false
% 27.64/3.99  --inst_eq_res_simp                      false
% 27.64/3.99  --inst_subs_given                       false
% 27.64/3.99  --inst_orphan_elimination               true
% 27.64/3.99  --inst_learning_loop_flag               true
% 27.64/3.99  --inst_learning_start                   3000
% 27.64/3.99  --inst_learning_factor                  2
% 27.64/3.99  --inst_start_prop_sim_after_learn       3
% 27.64/3.99  --inst_sel_renew                        solver
% 27.64/3.99  --inst_lit_activity_flag                true
% 27.64/3.99  --inst_restr_to_given                   false
% 27.64/3.99  --inst_activity_threshold               500
% 27.64/3.99  --inst_out_proof                        true
% 27.64/3.99  
% 27.64/3.99  ------ Resolution Options
% 27.64/3.99  
% 27.64/3.99  --resolution_flag                       false
% 27.64/3.99  --res_lit_sel                           adaptive
% 27.64/3.99  --res_lit_sel_side                      none
% 27.64/3.99  --res_ordering                          kbo
% 27.64/3.99  --res_to_prop_solver                    active
% 27.64/3.99  --res_prop_simpl_new                    false
% 27.64/3.99  --res_prop_simpl_given                  true
% 27.64/3.99  --res_passive_queue_type                priority_queues
% 27.64/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.64/3.99  --res_passive_queues_freq               [15;5]
% 27.64/3.99  --res_forward_subs                      full
% 27.64/3.99  --res_backward_subs                     full
% 27.64/3.99  --res_forward_subs_resolution           true
% 27.64/3.99  --res_backward_subs_resolution          true
% 27.64/3.99  --res_orphan_elimination                true
% 27.64/3.99  --res_time_limit                        2.
% 27.64/3.99  --res_out_proof                         true
% 27.64/3.99  
% 27.64/3.99  ------ Superposition Options
% 27.64/3.99  
% 27.64/3.99  --superposition_flag                    true
% 27.64/3.99  --sup_passive_queue_type                priority_queues
% 27.64/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.64/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.64/3.99  --demod_completeness_check              fast
% 27.64/3.99  --demod_use_ground                      true
% 27.64/3.99  --sup_to_prop_solver                    passive
% 27.64/3.99  --sup_prop_simpl_new                    true
% 27.64/3.99  --sup_prop_simpl_given                  true
% 27.64/3.99  --sup_fun_splitting                     false
% 27.64/3.99  --sup_smt_interval                      50000
% 27.64/3.99  
% 27.64/3.99  ------ Superposition Simplification Setup
% 27.64/3.99  
% 27.64/3.99  --sup_indices_passive                   []
% 27.64/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.64/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.64/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.64/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.64/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.64/3.99  --sup_full_bw                           [BwDemod]
% 27.64/3.99  --sup_immed_triv                        [TrivRules]
% 27.64/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.64/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.64/3.99  --sup_immed_bw_main                     []
% 27.64/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.64/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.64/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.64/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.64/3.99  
% 27.64/3.99  ------ Combination Options
% 27.64/3.99  
% 27.64/3.99  --comb_res_mult                         3
% 27.64/3.99  --comb_sup_mult                         2
% 27.64/3.99  --comb_inst_mult                        10
% 27.64/3.99  
% 27.64/3.99  ------ Debug Options
% 27.64/3.99  
% 27.64/3.99  --dbg_backtrace                         false
% 27.64/3.99  --dbg_dump_prop_clauses                 false
% 27.64/3.99  --dbg_dump_prop_clauses_file            -
% 27.64/3.99  --dbg_out_stat                          false
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  ------ Proving...
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  % SZS status Theorem for theBenchmark.p
% 27.64/3.99  
% 27.64/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.64/3.99  
% 27.64/3.99  fof(f10,axiom,(
% 27.64/3.99    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f33,plain,(
% 27.64/3.99    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f10])).
% 27.64/3.99  
% 27.64/3.99  fof(f34,plain,(
% 27.64/3.99    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f33])).
% 27.64/3.99  
% 27.64/3.99  fof(f85,plain,(
% 27.64/3.99    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f34])).
% 27.64/3.99  
% 27.64/3.99  fof(f13,conjecture,(
% 27.64/3.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f14,negated_conjecture,(
% 27.64/3.99    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 27.64/3.99    inference(negated_conjecture,[],[f13])).
% 27.64/3.99  
% 27.64/3.99  fof(f39,plain,(
% 27.64/3.99    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f14])).
% 27.64/3.99  
% 27.64/3.99  fof(f40,plain,(
% 27.64/3.99    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f39])).
% 27.64/3.99  
% 27.64/3.99  fof(f59,plain,(
% 27.64/3.99    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) | ~l3_lattices(sK6) | ~v13_lattices(sK6) | ~v10_lattices(sK6) | v2_struct_0(sK6)) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f60,plain,(
% 27.64/3.99    (k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) | ~l3_lattices(sK6) | ~v13_lattices(sK6) | ~v10_lattices(sK6) | v2_struct_0(sK6)) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 27.64/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f59])).
% 27.64/3.99  
% 27.64/3.99  fof(f94,plain,(
% 27.64/3.99    l3_lattices(sK6)),
% 27.64/3.99    inference(cnf_transformation,[],[f60])).
% 27.64/3.99  
% 27.64/3.99  fof(f91,plain,(
% 27.64/3.99    ~v2_struct_0(sK6)),
% 27.64/3.99    inference(cnf_transformation,[],[f60])).
% 27.64/3.99  
% 27.64/3.99  fof(f8,axiom,(
% 27.64/3.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f29,plain,(
% 27.64/3.99    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f8])).
% 27.64/3.99  
% 27.64/3.99  fof(f30,plain,(
% 27.64/3.99    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f29])).
% 27.64/3.99  
% 27.64/3.99  fof(f47,plain,(
% 27.64/3.99    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(nnf_transformation,[],[f30])).
% 27.64/3.99  
% 27.64/3.99  fof(f48,plain,(
% 27.64/3.99    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(rectify,[],[f47])).
% 27.64/3.99  
% 27.64/3.99  fof(f50,plain,(
% 27.64/3.99    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f49,plain,(
% 27.64/3.99    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f51,plain,(
% 27.64/3.99    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 27.64/3.99  
% 27.64/3.99  fof(f79,plain,(
% 27.64/3.99    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f51])).
% 27.64/3.99  
% 27.64/3.99  fof(f5,axiom,(
% 27.64/3.99    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f15,plain,(
% 27.64/3.99    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 27.64/3.99    inference(pure_predicate_removal,[],[f5])).
% 27.64/3.99  
% 27.64/3.99  fof(f24,plain,(
% 27.64/3.99    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 27.64/3.99    inference(ennf_transformation,[],[f15])).
% 27.64/3.99  
% 27.64/3.99  fof(f71,plain,(
% 27.64/3.99    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f24])).
% 27.64/3.99  
% 27.64/3.99  fof(f11,axiom,(
% 27.64/3.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f35,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f11])).
% 27.64/3.99  
% 27.64/3.99  fof(f36,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f35])).
% 27.64/3.99  
% 27.64/3.99  fof(f86,plain,(
% 27.64/3.99    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f36])).
% 27.64/3.99  
% 27.64/3.99  fof(f93,plain,(
% 27.64/3.99    v4_lattice3(sK6)),
% 27.64/3.99    inference(cnf_transformation,[],[f60])).
% 27.64/3.99  
% 27.64/3.99  fof(f92,plain,(
% 27.64/3.99    v10_lattices(sK6)),
% 27.64/3.99    inference(cnf_transformation,[],[f60])).
% 27.64/3.99  
% 27.64/3.99  fof(f76,plain,(
% 27.64/3.99    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f51])).
% 27.64/3.99  
% 27.64/3.99  fof(f80,plain,(
% 27.64/3.99    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f51])).
% 27.64/3.99  
% 27.64/3.99  fof(f1,axiom,(
% 27.64/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f61,plain,(
% 27.64/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f1])).
% 27.64/3.99  
% 27.64/3.99  fof(f2,axiom,(
% 27.64/3.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f19,plain,(
% 27.64/3.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 27.64/3.99    inference(ennf_transformation,[],[f2])).
% 27.64/3.99  
% 27.64/3.99  fof(f62,plain,(
% 27.64/3.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f19])).
% 27.64/3.99  
% 27.64/3.99  fof(f12,axiom,(
% 27.64/3.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f37,plain,(
% 27.64/3.99    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f12])).
% 27.64/3.99  
% 27.64/3.99  fof(f38,plain,(
% 27.64/3.99    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f37])).
% 27.64/3.99  
% 27.64/3.99  fof(f57,plain,(
% 27.64/3.99    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK5(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f58,plain,(
% 27.64/3.99    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK5(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f57])).
% 27.64/3.99  
% 27.64/3.99  fof(f89,plain,(
% 27.64/3.99    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK5(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f58])).
% 27.64/3.99  
% 27.64/3.99  fof(f6,axiom,(
% 27.64/3.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f25,plain,(
% 27.64/3.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f6])).
% 27.64/3.99  
% 27.64/3.99  fof(f26,plain,(
% 27.64/3.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f25])).
% 27.64/3.99  
% 27.64/3.99  fof(f45,plain,(
% 27.64/3.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(nnf_transformation,[],[f26])).
% 27.64/3.99  
% 27.64/3.99  fof(f72,plain,(
% 27.64/3.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f45])).
% 27.64/3.99  
% 27.64/3.99  fof(f3,axiom,(
% 27.64/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f16,plain,(
% 27.64/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 27.64/3.99    inference(pure_predicate_removal,[],[f3])).
% 27.64/3.99  
% 27.64/3.99  fof(f17,plain,(
% 27.64/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 27.64/3.99    inference(pure_predicate_removal,[],[f16])).
% 27.64/3.99  
% 27.64/3.99  fof(f18,plain,(
% 27.64/3.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 27.64/3.99    inference(pure_predicate_removal,[],[f17])).
% 27.64/3.99  
% 27.64/3.99  fof(f20,plain,(
% 27.64/3.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 27.64/3.99    inference(ennf_transformation,[],[f18])).
% 27.64/3.99  
% 27.64/3.99  fof(f21,plain,(
% 27.64/3.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 27.64/3.99    inference(flattening,[],[f20])).
% 27.64/3.99  
% 27.64/3.99  fof(f66,plain,(
% 27.64/3.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f21])).
% 27.64/3.99  
% 27.64/3.99  fof(f64,plain,(
% 27.64/3.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f21])).
% 27.64/3.99  
% 27.64/3.99  fof(f65,plain,(
% 27.64/3.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f21])).
% 27.64/3.99  
% 27.64/3.99  fof(f7,axiom,(
% 27.64/3.99    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f27,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f7])).
% 27.64/3.99  
% 27.64/3.99  fof(f28,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f27])).
% 27.64/3.99  
% 27.64/3.99  fof(f46,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(nnf_transformation,[],[f28])).
% 27.64/3.99  
% 27.64/3.99  fof(f74,plain,(
% 27.64/3.99    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f46])).
% 27.64/3.99  
% 27.64/3.99  fof(f9,axiom,(
% 27.64/3.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f31,plain,(
% 27.64/3.99    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f9])).
% 27.64/3.99  
% 27.64/3.99  fof(f32,plain,(
% 27.64/3.99    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f31])).
% 27.64/3.99  
% 27.64/3.99  fof(f52,plain,(
% 27.64/3.99    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(nnf_transformation,[],[f32])).
% 27.64/3.99  
% 27.64/3.99  fof(f53,plain,(
% 27.64/3.99    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(rectify,[],[f52])).
% 27.64/3.99  
% 27.64/3.99  fof(f55,plain,(
% 27.64/3.99    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK4(X0)) != k2_lattices(X0,sK4(X0),X1) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f54,plain,(
% 27.64/3.99    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK3(X0)) != k2_lattices(X0,sK3(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f56,plain,(
% 27.64/3.99    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK3(X0),sK4(X0)) != k2_lattices(X0,sK4(X0),sK3(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).
% 27.64/3.99  
% 27.64/3.99  fof(f81,plain,(
% 27.64/3.99    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f56])).
% 27.64/3.99  
% 27.64/3.99  fof(f78,plain,(
% 27.64/3.99    ( ! [X4,X0] : (k2_lattices(X0,X4,sK2(X0)) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f51])).
% 27.64/3.99  
% 27.64/3.99  fof(f95,plain,(
% 27.64/3.99    k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) | ~l3_lattices(sK6) | ~v13_lattices(sK6) | ~v10_lattices(sK6) | v2_struct_0(sK6)),
% 27.64/3.99    inference(cnf_transformation,[],[f60])).
% 27.64/3.99  
% 27.64/3.99  fof(f4,axiom,(
% 27.64/3.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 27.64/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.64/3.99  
% 27.64/3.99  fof(f22,plain,(
% 27.64/3.99    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 27.64/3.99    inference(ennf_transformation,[],[f4])).
% 27.64/3.99  
% 27.64/3.99  fof(f23,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(flattening,[],[f22])).
% 27.64/3.99  
% 27.64/3.99  fof(f41,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(nnf_transformation,[],[f23])).
% 27.64/3.99  
% 27.64/3.99  fof(f42,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(rectify,[],[f41])).
% 27.64/3.99  
% 27.64/3.99  fof(f43,plain,(
% 27.64/3.99    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 27.64/3.99    introduced(choice_axiom,[])).
% 27.64/3.99  
% 27.64/3.99  fof(f44,plain,(
% 27.64/3.99    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 27.64/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 27.64/3.99  
% 27.64/3.99  fof(f69,plain,(
% 27.64/3.99    ( ! [X0,X1] : (k5_lattices(X0) = X1 | m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f44])).
% 27.64/3.99  
% 27.64/3.99  fof(f70,plain,(
% 27.64/3.99    ( ! [X0,X1] : (k5_lattices(X0) = X1 | k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f44])).
% 27.64/3.99  
% 27.64/3.99  fof(f77,plain,(
% 27.64/3.99    ( ! [X4,X0] : (k2_lattices(X0,sK2(X0),X4) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 27.64/3.99    inference(cnf_transformation,[],[f51])).
% 27.64/3.99  
% 27.64/3.99  cnf(c_24,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f85]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_31,negated_conjecture,
% 27.64/3.99      ( l3_lattices(sK6) ),
% 27.64/3.99      inference(cnf_transformation,[],[f94]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_773,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_774,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | v2_struct_0(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_773]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_34,negated_conjecture,
% 27.64/3.99      ( ~ v2_struct_0(sK6) ),
% 27.64/3.99      inference(cnf_transformation,[],[f91]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_778,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6)) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_774,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2128,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_778]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2528,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_16,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | v13_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1) ),
% 27.64/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1039,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | v13_lattices(X1)
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1040,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | v13_lattices(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_1039]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_10,plain,
% 27.64/3.99      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f71]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_98,plain,
% 27.64/3.99      ( l1_lattices(sK6) | ~ l3_lattices(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_10]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1044,plain,
% 27.64/3.99      ( m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_1040,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1045,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6) ),
% 27.64/3.99      inference(renaming,[status(thm)],[c_1044]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2121,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK1(sK6,X0_57),u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_1045]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2535,plain,
% 27.64/3.99      ( m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | m1_subset_1(sK1(sK6,X0_57),u1_struct_0(sK6)) = iProver_top
% 27.64/3.99      | v13_lattices(sK6) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2121]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_26,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ v4_lattice3(X1)
% 27.64/3.99      | ~ l3_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | ~ v10_lattices(X1)
% 27.64/3.99      | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0 ),
% 27.64/3.99      inference(cnf_transformation,[],[f86]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_32,negated_conjecture,
% 27.64/3.99      ( v4_lattice3(sK6) ),
% 27.64/3.99      inference(cnf_transformation,[],[f93]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_530,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l3_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | ~ v10_lattices(X1)
% 27.64/3.99      | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_531,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | ~ v10_lattices(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,X0)) = X0 ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_530]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_33,negated_conjecture,
% 27.64/3.99      ( v10_lattices(sK6) ),
% 27.64/3.99      inference(cnf_transformation,[],[f92]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_535,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,X0)) = X0 ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_531,c_34,c_33,c_31]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2132,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,X0_57)) = X0_57 ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_535]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2524,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,X0_57)) = X0_57
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2132]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3386,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,X0_57))) = sK1(sK6,X0_57)
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) = iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2535,c_2524]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4591,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)))) = sK1(sK6,k15_lattice3(sK6,X0_60))
% 27.64/3.99      | v13_lattices(sK6) = iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2528,c_3386]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_19,plain,
% 27.64/3.99      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 27.64/3.99      | ~ l1_lattices(X0)
% 27.64/3.99      | ~ v13_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_965,plain,
% 27.64/3.99      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 27.64/3.99      | ~ l1_lattices(X0)
% 27.64/3.99      | ~ v13_lattices(X0)
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_966,plain,
% 27.64/3.99      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | ~ v13_lattices(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_965]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_968,plain,
% 27.64/3.99      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) | ~ v13_lattices(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_966,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2124,plain,
% 27.64/3.99      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) | ~ v13_lattices(sK6) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_968]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2532,plain,
% 27.64/3.99      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2124]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2743,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6)
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2532,c_2524]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4632,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)))) = sK1(sK6,k15_lattice3(sK6,X0_60))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_4591,c_2743]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_59397,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(sK1(sK6,k15_lattice3(sK6,X0_60)),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_4632,c_2528]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2174,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2176,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2174]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_15,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | v13_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 27.64/3.99      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 27.64/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1060,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | v13_lattices(X1)
% 27.64/3.99      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 27.64/3.99      | k2_lattices(X1,sK1(X1,X0),X0) != X0
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1061,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_1060]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1065,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_1061,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2120,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0_57,sK1(sK6,X0_57)) != X0_57
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,X0_57),X0_57) != X0_57 ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_1065]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2727,plain,
% 27.64/3.99      ( ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK1(sK6,k15_lattice3(sK6,X0_60))) != k15_lattice3(sK6,X0_60)
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,X0_60)) != k15_lattice3(sK6,X0_60) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2120]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2728,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK1(sK6,k15_lattice3(sK6,X0_60))) != k15_lattice3(sK6,X0_60)
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,X0_60)) != k15_lattice3(sK6,X0_60)
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2727]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2730,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) = iProver_top ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2728]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_0,plain,
% 27.64/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1,plain,
% 27.64/3.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_391,plain,
% 27.64/3.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_392,plain,
% 27.64/3.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_391]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_28,plain,
% 27.64/3.99      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 27.64/3.99      | r2_hidden(sK5(X0,X1,X2),X1)
% 27.64/3.99      | ~ v4_lattice3(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v10_lattices(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f89]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_488,plain,
% 27.64/3.99      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 27.64/3.99      | r2_hidden(sK5(X0,X1,X2),X1)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v10_lattices(X0)
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_489,plain,
% 27.64/3.99      ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
% 27.64/3.99      | r2_hidden(sK5(sK6,X0,X1),X0)
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | ~ v10_lattices(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_488]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_493,plain,
% 27.64/3.99      ( r2_hidden(sK5(sK6,X0,X1),X0)
% 27.64/3.99      | r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1)) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_489,c_34,c_33,c_31]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_494,plain,
% 27.64/3.99      ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
% 27.64/3.99      | r2_hidden(sK5(sK6,X0,X1),X0) ),
% 27.64/3.99      inference(renaming,[status(thm)],[c_493]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_603,plain,
% 27.64/3.99      ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
% 27.64/3.99      | sK5(sK6,X0,X1) != X2
% 27.64/3.99      | k1_xboole_0 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_392,c_494]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_604,plain,
% 27.64/3.99      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0)) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_603]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2129,plain,
% 27.64/3.99      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_604]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2527,plain,
% 27.64/3.99      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2129]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_12,plain,
% 27.64/3.99      ( r1_lattices(X0,X1,X2)
% 27.64/3.99      | ~ r3_lattices(X0,X1,X2)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.64/3.99      | ~ v6_lattices(X0)
% 27.64/3.99      | ~ v8_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v9_lattices(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2,plain,
% 27.64/3.99      ( ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v10_lattices(X0)
% 27.64/3.99      | v9_lattices(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_640,plain,
% 27.64/3.99      ( ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | v9_lattices(X0)
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_2,c_33]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_641,plain,
% 27.64/3.99      ( ~ l3_lattices(sK6) | v2_struct_0(sK6) | v9_lattices(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_640]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_120,plain,
% 27.64/3.99      ( ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | ~ v10_lattices(sK6)
% 27.64/3.99      | v9_lattices(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_643,plain,
% 27.64/3.99      ( v9_lattices(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_641,c_34,c_33,c_31,c_120]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_705,plain,
% 27.64/3.99      ( r1_lattices(X0,X1,X2)
% 27.64/3.99      | ~ r3_lattices(X0,X1,X2)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.64/3.99      | ~ v6_lattices(X0)
% 27.64/3.99      | ~ v8_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_12,c_643]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_706,plain,
% 27.64/3.99      ( r1_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ r3_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ v6_lattices(sK6)
% 27.64/3.99      | ~ v8_lattices(sK6)
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_705]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4,plain,
% 27.64/3.99      ( v6_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v10_lattices(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114,plain,
% 27.64/3.99      ( v6_lattices(sK6)
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | ~ v10_lattices(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3,plain,
% 27.64/3.99      ( v8_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v10_lattices(X0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_117,plain,
% 27.64/3.99      ( v8_lattices(sK6)
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | ~ v10_lattices(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_710,plain,
% 27.64/3.99      ( r1_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ r3_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_706,c_34,c_33,c_31,c_114,c_117]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_711,plain,
% 27.64/3.99      ( r1_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ r3_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 27.64/3.99      inference(renaming,[status(thm)],[c_710]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_14,plain,
% 27.64/3.99      ( ~ r1_lattices(X0,X1,X2)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.64/3.99      | ~ v8_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | ~ v9_lattices(X0)
% 27.64/3.99      | k2_lattices(X0,X1,X2) = X1 ),
% 27.64/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_657,plain,
% 27.64/3.99      ( ~ r1_lattices(X0,X1,X2)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.64/3.99      | ~ v8_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | k2_lattices(X0,X1,X2) = X1
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_14,c_643]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_658,plain,
% 27.64/3.99      ( ~ r1_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ v8_lattices(sK6)
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,X1) = X0 ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_657]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_662,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | ~ r1_lattices(sK6,X0,X1)
% 27.64/3.99      | k2_lattices(sK6,X0,X1) = X0 ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_658,c_34,c_33,c_31,c_117]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_663,plain,
% 27.64/3.99      ( ~ r1_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,X0,X1) = X0 ),
% 27.64/3.99      inference(renaming,[status(thm)],[c_662]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_800,plain,
% 27.64/3.99      ( ~ r3_lattices(sK6,X0,X1)
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,X0,X1) = X0 ),
% 27.64/3.99      inference(resolution,[status(thm)],[c_711,c_663]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2127,plain,
% 27.64/3.99      ( ~ r3_lattices(sK6,X0_57,X1_57)
% 27.64/3.99      | ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1_57,u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,X0_57,X1_57) = X0_57 ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_800]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2529,plain,
% 27.64/3.99      ( k2_lattices(sK6,X0_57,X1_57) = X0_57
% 27.64/3.99      | r3_lattices(sK6,X0_57,X1_57) != iProver_top
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2127]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4479,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2527,c_2529]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2175,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2128]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2753,plain,
% 27.64/3.99      ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_60),X0_57)
% 27.64/3.99      | ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,k15_lattice3(sK6,X0_60),X0_57) = k15_lattice3(sK6,X0_60) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2127]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3074,plain,
% 27.64/3.99      ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,X1_60))
% 27.64/3.99      | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(k15_lattice3(sK6,X1_60),u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,X1_60)) = k15_lattice3(sK6,X0_60) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2753]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3813,plain,
% 27.64/3.99      ( ~ r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60))
% 27.64/3.99      | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3074]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_14817,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_60)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_4479,c_2129,c_2128,c_2175,c_3813]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_23,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v6_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 27.64/3.99      inference(cnf_transformation,[],[f81]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_979,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v6_lattices(X1)
% 27.64/3.99      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_980,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | ~ v6_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_979]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_618,plain,
% 27.64/3.99      ( v6_lattices(X0)
% 27.64/3.99      | ~ l3_lattices(X0)
% 27.64/3.99      | v2_struct_0(X0)
% 27.64/3.99      | sK6 != X0 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_4,c_33]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_619,plain,
% 27.64/3.99      ( v6_lattices(sK6) | ~ l3_lattices(sK6) | v2_struct_0(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_618]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_621,plain,
% 27.64/3.99      ( v6_lattices(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_619,c_34,c_33,c_31,c_114]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_917,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_23,c_621]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_918,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_917]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_983,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_980,c_34,c_31,c_98,c_918]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2125,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X1_57,u1_struct_0(sK6))
% 27.64/3.99      | k2_lattices(sK6,X1_57,X0_57) = k2_lattices(sK6,X0_57,X1_57) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_983]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2531,plain,
% 27.64/3.99      ( k2_lattices(sK6,X0_57,X1_57) = k2_lattices(sK6,X1_57,X0_57)
% 27.64/3.99      | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3043,plain,
% 27.64/3.99      ( k2_lattices(sK6,X0_57,k15_lattice3(sK6,X0_60)) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),X0_57)
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2528,c_2531]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4126,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,X1_60)) = k2_lattices(sK6,k15_lattice3(sK6,X1_60),k15_lattice3(sK6,X0_60)) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2528,c_3043]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_14825,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_14817,c_4126]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_59375,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_4632,c_14825]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60166,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_59375]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_59376,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,X0_60))) = k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_4632,c_14817]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60167,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) = k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_59376]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60268,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_59397,c_2176,c_2730,c_2743,c_60166,c_60167]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60317,plain,
% 27.64/3.99      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_60268,c_2528]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_61182,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6))
% 27.64/3.99      | v13_lattices(sK6) = iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_60317,c_3386]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_17,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
% 27.64/3.99      inference(cnf_transformation,[],[f78]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1018,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1019,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,sK2(sK6)) = sK2(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_1018]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1023,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,sK2(sK6)) = sK2(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_1019,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2122,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0_57,sK2(sK6)) = sK2(sK6) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_1023]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2534,plain,
% 27.64/3.99      ( k2_lattices(sK6,X0_57,sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3030,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_2528,c_2534]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_91291,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_61182,c_3030]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2147,plain,
% 27.64/3.99      ( X0_60 != X1_60
% 27.64/3.99      | k15_lattice3(X0_59,X0_60) = k15_lattice3(X0_59,X1_60) ),
% 27.64/3.99      theory(equality) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2152,plain,
% 27.64/3.99      ( k1_xboole_0 != k1_xboole_0
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2147]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2141,plain,( X0_60 = X0_60 ),theory(equality) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2156,plain,
% 27.64/3.99      ( k1_xboole_0 = k1_xboole_0 ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2141]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_30,negated_conjecture,
% 27.64/3.99      ( ~ v13_lattices(sK6)
% 27.64/3.99      | ~ l3_lattices(sK6)
% 27.64/3.99      | v2_struct_0(sK6)
% 27.64/3.99      | ~ v10_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(cnf_transformation,[],[f95]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_203,negated_conjecture,
% 27.64/3.99      ( ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_30,c_34,c_33,c_31]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2134,negated_conjecture,
% 27.64/3.99      ( ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_203]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2158,plain,
% 27.64/3.99      ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_7,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k5_lattices(X1) = X0 ),
% 27.64/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1132,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | k5_lattices(X1) = X0
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1133,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK0(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) = X0 ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_1132]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1137,plain,
% 27.64/3.99      ( m1_subset_1(sK0(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) = X0 ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_1133,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1138,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK0(sK6,X0),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) = X0 ),
% 27.64/3.99      inference(renaming,[status(thm)],[c_1137]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2117,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK0(sK6,X0_57),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) = X0_57 ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_1138]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2903,plain,
% 27.64/3.99      ( m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(sK2(sK6),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k5_lattices(sK6) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2117]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2904,plain,
% 27.64/3.99      ( k5_lattices(sK6) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6)) = iProver_top
% 27.64/3.99      | m1_subset_1(sK2(sK6),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2903]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_6,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k2_lattices(X1,X0,sK0(X1,X0)) != X0
% 27.64/3.99      | k2_lattices(X1,sK0(X1,X0),X0) != X0
% 27.64/3.99      | k5_lattices(X1) = X0 ),
% 27.64/3.99      inference(cnf_transformation,[],[f70]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1156,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | k2_lattices(X1,X0,sK0(X1,X0)) != X0
% 27.64/3.99      | k2_lattices(X1,sK0(X1,X0),X0) != X0
% 27.64/3.99      | k5_lattices(X1) = X0
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1157,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,sK0(sK6,X0)) != X0
% 27.64/3.99      | k2_lattices(sK6,sK0(sK6,X0),X0) != X0
% 27.64/3.99      | k5_lattices(sK6) = X0 ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_1156]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1161,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0,sK0(sK6,X0)) != X0
% 27.64/3.99      | k2_lattices(sK6,sK0(sK6,X0),X0) != X0
% 27.64/3.99      | k5_lattices(sK6) = X0 ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_1157,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2116,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,X0_57,sK0(sK6,X0_57)) != X0_57
% 27.64/3.99      | k2_lattices(sK6,sK0(sK6,X0_57),X0_57) != X0_57
% 27.64/3.99      | k5_lattices(sK6) = X0_57 ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_1161]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3490,plain,
% 27.64/3.99      ( ~ m1_subset_1(sK2(sK6),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK0(sK6,sK2(sK6)),sK2(sK6)) != sK2(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK2(sK6),sK0(sK6,sK2(sK6))) != sK2(sK6)
% 27.64/3.99      | k5_lattices(sK6) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2116]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2143,plain,
% 27.64/3.99      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 27.64/3.99      theory(equality) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2825,plain,
% 27.64/3.99      ( X0_57 != X1_57
% 27.64/3.99      | X0_57 = k15_lattice3(sK6,X0_60)
% 27.64/3.99      | k15_lattice3(sK6,X0_60) != X1_57 ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2143]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3237,plain,
% 27.64/3.99      ( X0_57 = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | X0_57 != sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2825]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3824,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6)
% 27.64/3.99      | sK2(sK6) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | sK2(sK6) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3237]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2140,plain,( X0_57 = X0_57 ),theory(equality) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3825,plain,
% 27.64/3.99      ( sK2(sK6) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2140]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3834,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6)
% 27.64/3.99      | k5_lattices(sK6) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k5_lattices(sK6) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3237]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4999,plain,
% 27.64/3.99      ( ~ m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK0(sK6,sK2(sK6)),sK2(sK6)) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2122]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_5022,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK0(sK6,sK2(sK6)),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_4999]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_18,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | v2_struct_0(X1)
% 27.64/3.99      | k2_lattices(X1,sK2(X1),X0) = sK2(X1) ),
% 27.64/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_997,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.64/3.99      | ~ l1_lattices(X1)
% 27.64/3.99      | ~ v13_lattices(X1)
% 27.64/3.99      | k2_lattices(X1,sK2(X1),X0) = sK2(X1)
% 27.64/3.99      | sK6 != X1 ),
% 27.64/3.99      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_998,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ l1_lattices(sK6)
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK2(sK6),X0) = sK2(sK6) ),
% 27.64/3.99      inference(unflattening,[status(thm)],[c_997]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_1002,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK2(sK6),X0) = sK2(sK6) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_998,c_31,c_98]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2123,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK2(sK6),X0_57) = sK2(sK6) ),
% 27.64/3.99      inference(subtyping,[status(esa)],[c_1002]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4998,plain,
% 27.64/3.99      ( ~ m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK2(sK6),sK0(sK6,sK2(sK6))) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2123]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_5024,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),sK0(sK6,sK2(sK6))) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(sK0(sK6,sK2(sK6)),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_4998]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3232,plain,
% 27.64/3.99      ( X0_57 != X1_57
% 27.64/3.99      | k15_lattice3(sK6,X0_60) != X1_57
% 27.64/3.99      | k15_lattice3(sK6,X0_60) = X0_57 ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2143]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3776,plain,
% 27.64/3.99      ( X0_57 != sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = X0_57
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3232]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_5769,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) != sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3776]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_5770,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) != sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_5769]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3241,plain,
% 27.64/3.99      ( X0_57 != k15_lattice3(sK6,X0_60)
% 27.64/3.99      | X0_57 = k15_lattice3(sK6,X1_60)
% 27.64/3.99      | k15_lattice3(sK6,X1_60) != k15_lattice3(sK6,X0_60) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2825]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_8372,plain,
% 27.64/3.99      ( k15_lattice3(sK6,X0_60) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k5_lattices(sK6) = k15_lattice3(sK6,X0_60)
% 27.64/3.99      | k5_lattices(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3241]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_8388,plain,
% 27.64/3.99      ( k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k5_lattices(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k5_lattices(sK6) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_8372]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_8584,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6)) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2128]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_8585,plain,
% 27.64/3.99      ( m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_8584]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_3772,plain,
% 27.64/3.99      ( X0_57 != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = X0_57
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3232]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_30346,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3772]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_30349,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_30346]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2145,plain,
% 27.64/3.99      ( ~ m1_subset_1(X0_57,X0_58)
% 27.64/3.99      | m1_subset_1(X1_57,X0_58)
% 27.64/3.99      | X1_57 != X0_57 ),
% 27.64/3.99      theory(equality) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2758,plain,
% 27.64/3.99      ( m1_subset_1(X0_57,u1_struct_0(sK6))
% 27.64/3.99      | ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
% 27.64/3.99      | X0_57 != k15_lattice3(sK6,X0_60) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2145]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_52661,plain,
% 27.64/3.99      ( ~ m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6))
% 27.64/3.99      | m1_subset_1(sK2(sK6),u1_struct_0(sK6))
% 27.64/3.99      | sK2(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2758]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_52662,plain,
% 27.64/3.99      ( sK2(sK6) != k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_52661]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60295,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_60268,c_14825]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_4628,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X1_60)))) = sK1(sK6,k15_lattice3(sK6,X1_60)) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_4591,c_3030]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60334,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_60268,c_4628]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60669,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
% 27.64/3.99      inference(light_normalisation,[status(thm)],[c_60334,c_60268]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60371,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))),k15_lattice3(sK6,X0_60)) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_60268,c_4126]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60466,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) ),
% 27.64/3.99      inference(light_normalisation,[status(thm)],[c_60371,c_60268]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60670,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X0_60)) = sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
% 27.64/3.99      inference(demodulation,[status(thm)],[c_60669,c_60466]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_61017,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0)) = sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_60670]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_61528,plain,
% 27.64/3.99      ( v13_lattices(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
% 27.64/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_61182]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_33550,plain,
% 27.64/3.99      ( k15_lattice3(sK6,X0_60) != X0_57
% 27.64/3.99      | k15_lattice3(sK6,X0_60) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != X0_57 ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2825]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114159,plain,
% 27.64/3.99      ( k15_lattice3(sK6,X0_60) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X1_60))
% 27.64/3.99      | k15_lattice3(sK6,X0_60) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,X1_60)) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_33550]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114160,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k2_lattices(sK6,sK2(sK6),k15_lattice3(sK6,k1_xboole_0))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_114159]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114377,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,sK2(sK6)))) = sK1(sK6,sK2(sK6)) ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_91291,c_2152,c_2156,c_2158,c_2176,c_2730,c_2743,
% 27.64/3.99                 c_2904,c_3490,c_3824,c_3825,c_3834,c_5022,c_5024,c_5770,
% 27.64/3.99                 c_8388,c_8584,c_8585,c_30349,c_52661,c_52662,c_60166,
% 27.64/3.99                 c_60167,c_60295,c_61017,c_61182,c_61528,c_114160]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114432,plain,
% 27.64/3.99      ( m1_subset_1(sK1(sK6,sK2(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_114377,c_2528]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_115442,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK1(sK6,sK2(sK6)),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_114432,c_2534]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2840,plain,
% 27.64/3.99      ( ~ m1_subset_1(sK2(sK6),u1_struct_0(sK6))
% 27.64/3.99      | v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK1(sK6,sK2(sK6)),sK2(sK6)) != sK2(sK6)
% 27.64/3.99      | k2_lattices(sK6,sK2(sK6),sK1(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2120]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2892,plain,
% 27.64/3.99      ( ~ m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6))
% 27.64/3.99      | ~ v13_lattices(sK6)
% 27.64/3.99      | k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2122]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2893,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,X0_60),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2892]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2895,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_2893]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_5767,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) != sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3776]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_5768,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) != sK2(sK6)
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != sK2(sK6) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_5767]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_30341,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6)) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,k15_lattice3(sK6,X0_60),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_3772]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_30344,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) != k15_lattice3(sK6,k1_xboole_0)
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_30341]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_60296,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_60268,c_14817]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114157,plain,
% 27.64/3.99      ( k15_lattice3(sK6,X0_60) != k2_lattices(sK6,k15_lattice3(sK6,X1_60),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,X0_60) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6)))
% 27.64/3.99      | k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,k15_lattice3(sK6,X1_60),sK2(sK6)) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_33550]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_114158,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK2(sK6))
% 27.64/3.99      | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,a_2_3_lattice3(sK6,sK2(sK6))) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_114157]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_2533,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),X0_57) = sK2(sK6)
% 27.64/3.99      | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_115443,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK2(sK6),sK1(sK6,sK2(sK6))) = sK2(sK6)
% 27.64/3.99      | v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_114432,c_2533]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_115906,plain,
% 27.64/3.99      ( v13_lattices(sK6) != iProver_top ),
% 27.64/3.99      inference(global_propositional_subsumption,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_115442,c_2152,c_2156,c_2158,c_2176,c_2730,c_2743,
% 27.64/3.99                 c_2840,c_2895,c_2904,c_3490,c_3824,c_3825,c_3834,c_5022,
% 27.64/3.99                 c_5024,c_5768,c_8388,c_8584,c_8585,c_30344,c_52661,
% 27.64/3.99                 c_52662,c_60166,c_60167,c_60296,c_114158,c_115443]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_115989,plain,
% 27.64/3.99      ( k15_lattice3(sK6,a_2_3_lattice3(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)))) = sK1(sK6,k15_lattice3(sK6,X0_60)) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_4591,c_115906]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_119311,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,X0_60))) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_115989,c_14817]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_119939,plain,
% 27.64/3.99      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_119311]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_119310,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_60)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(superposition,[status(thm)],[c_115989,c_14825]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(c_119938,plain,
% 27.64/3.99      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 27.64/3.99      inference(instantiation,[status(thm)],[c_119310]) ).
% 27.64/3.99  
% 27.64/3.99  cnf(contradiction,plain,
% 27.64/3.99      ( $false ),
% 27.64/3.99      inference(minisat,
% 27.64/3.99                [status(thm)],
% 27.64/3.99                [c_119939,c_119938,c_115906,c_2730,c_2176]) ).
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.64/3.99  
% 27.64/3.99  ------                               Statistics
% 27.64/3.99  
% 27.64/3.99  ------ General
% 27.64/3.99  
% 27.64/3.99  abstr_ref_over_cycles:                  0
% 27.64/3.99  abstr_ref_under_cycles:                 0
% 27.64/3.99  gc_basic_clause_elim:                   0
% 27.64/3.99  forced_gc_time:                         0
% 27.64/3.99  parsing_time:                           0.009
% 27.64/3.99  unif_index_cands_time:                  0.
% 27.64/3.99  unif_index_add_time:                    0.
% 27.64/3.99  orderings_time:                         0.
% 27.64/3.99  out_proof_time:                         0.025
% 27.64/3.99  total_time:                             3.048
% 27.64/3.99  num_of_symbols:                         64
% 27.64/3.99  num_of_terms:                           52363
% 27.64/3.99  
% 27.64/3.99  ------ Preprocessing
% 27.64/3.99  
% 27.64/3.99  num_of_splits:                          2
% 27.64/3.99  num_of_split_atoms:                     2
% 27.64/3.99  num_of_reused_defs:                     0
% 27.64/3.99  num_eq_ax_congr_red:                    53
% 27.64/3.99  num_of_sem_filtered_clauses:            1
% 27.64/3.99  num_of_subtypes:                        5
% 27.64/3.99  monotx_restored_types:                  0
% 27.64/3.99  sat_num_of_epr_types:                   0
% 27.64/3.99  sat_num_of_non_cyclic_types:            0
% 27.64/3.99  sat_guarded_non_collapsed_types:        1
% 27.64/3.99  num_pure_diseq_elim:                    0
% 27.64/3.99  simp_replaced_by:                       0
% 27.64/3.99  res_preprocessed:                       114
% 27.64/3.99  prep_upred:                             0
% 27.64/3.99  prep_unflattend:                        41
% 27.64/3.99  smt_new_axioms:                         0
% 27.64/3.99  pred_elim_cands:                        3
% 27.64/3.99  pred_elim:                              11
% 27.64/3.99  pred_elim_cl:                           15
% 27.64/3.99  pred_elim_cycles:                       15
% 27.64/3.99  merged_defs:                            0
% 27.64/3.99  merged_defs_ncl:                        0
% 27.64/3.99  bin_hyper_res:                          0
% 27.64/3.99  prep_cycles:                            4
% 27.64/3.99  pred_elim_time:                         0.03
% 27.64/3.99  splitting_time:                         0.
% 27.64/3.99  sem_filter_time:                        0.
% 27.64/3.99  monotx_time:                            0.
% 27.64/3.99  subtype_inf_time:                       0.
% 27.64/3.99  
% 27.64/3.99  ------ Problem properties
% 27.64/3.99  
% 27.64/3.99  clauses:                                21
% 27.64/3.99  conjectures:                            1
% 27.64/3.99  epr:                                    0
% 27.64/3.99  horn:                                   17
% 27.64/3.99  ground:                                 4
% 27.64/3.99  unary:                                  2
% 27.64/3.99  binary:                                 5
% 27.64/3.99  lits:                                   60
% 27.64/3.99  lits_eq:                                16
% 27.64/3.99  fd_pure:                                0
% 27.64/3.99  fd_pseudo:                              0
% 27.64/3.99  fd_cond:                                2
% 27.64/3.99  fd_pseudo_cond:                         0
% 27.64/3.99  ac_symbols:                             0
% 27.64/3.99  
% 27.64/3.99  ------ Propositional Solver
% 27.64/3.99  
% 27.64/3.99  prop_solver_calls:                      36
% 27.64/3.99  prop_fast_solver_calls:                 2522
% 27.64/3.99  smt_solver_calls:                       0
% 27.64/3.99  smt_fast_solver_calls:                  0
% 27.64/3.99  prop_num_of_clauses:                    35251
% 27.64/3.99  prop_preprocess_simplified:             32482
% 27.64/3.99  prop_fo_subsumed:                       80
% 27.64/3.99  prop_solver_time:                       0.
% 27.64/3.99  smt_solver_time:                        0.
% 27.64/3.99  smt_fast_solver_time:                   0.
% 27.64/3.99  prop_fast_solver_time:                  0.
% 27.64/3.99  prop_unsat_core_time:                   0.002
% 27.64/3.99  
% 27.64/3.99  ------ QBF
% 27.64/3.99  
% 27.64/3.99  qbf_q_res:                              0
% 27.64/3.99  qbf_num_tautologies:                    0
% 27.64/3.99  qbf_prep_cycles:                        0
% 27.64/3.99  
% 27.64/3.99  ------ BMC1
% 27.64/3.99  
% 27.64/3.99  bmc1_current_bound:                     -1
% 27.64/3.99  bmc1_last_solved_bound:                 -1
% 27.64/3.99  bmc1_unsat_core_size:                   -1
% 27.64/3.99  bmc1_unsat_core_parents_size:           -1
% 27.64/3.99  bmc1_merge_next_fun:                    0
% 27.64/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.64/3.99  
% 27.64/3.99  ------ Instantiation
% 27.64/3.99  
% 27.64/3.99  inst_num_of_clauses:                    4650
% 27.64/3.99  inst_num_in_passive:                    805
% 27.64/3.99  inst_num_in_active:                     1536
% 27.64/3.99  inst_num_in_unprocessed:                2311
% 27.64/3.99  inst_num_of_loops:                      2140
% 27.64/3.99  inst_num_of_learning_restarts:          0
% 27.64/3.99  inst_num_moves_active_passive:          601
% 27.64/3.99  inst_lit_activity:                      0
% 27.64/3.99  inst_lit_activity_moves:                2
% 27.64/3.99  inst_num_tautologies:                   0
% 27.64/3.99  inst_num_prop_implied:                  0
% 27.64/3.99  inst_num_existing_simplified:           0
% 27.64/3.99  inst_num_eq_res_simplified:             0
% 27.64/3.99  inst_num_child_elim:                    0
% 27.64/3.99  inst_num_of_dismatching_blockings:      4473
% 27.64/3.99  inst_num_of_non_proper_insts:           5296
% 27.64/3.99  inst_num_of_duplicates:                 0
% 27.64/3.99  inst_inst_num_from_inst_to_res:         0
% 27.64/3.99  inst_dismatching_checking_time:         0.
% 27.64/3.99  
% 27.64/3.99  ------ Resolution
% 27.64/3.99  
% 27.64/3.99  res_num_of_clauses:                     0
% 27.64/3.99  res_num_in_passive:                     0
% 27.64/3.99  res_num_in_active:                      0
% 27.64/3.99  res_num_of_loops:                       118
% 27.64/3.99  res_forward_subset_subsumed:            648
% 27.64/3.99  res_backward_subset_subsumed:           8
% 27.64/3.99  res_forward_subsumed:                   0
% 27.64/3.99  res_backward_subsumed:                  0
% 27.64/3.99  res_forward_subsumption_resolution:     1
% 27.64/3.99  res_backward_subsumption_resolution:    0
% 27.64/3.99  res_clause_to_clause_subsumption:       28363
% 27.64/3.99  res_orphan_elimination:                 0
% 27.64/3.99  res_tautology_del:                      462
% 27.64/3.99  res_num_eq_res_simplified:              0
% 27.64/3.99  res_num_sel_changes:                    0
% 27.64/3.99  res_moves_from_active_to_pass:          0
% 27.64/3.99  
% 27.64/3.99  ------ Superposition
% 27.64/3.99  
% 27.64/3.99  sup_time_total:                         0.
% 27.64/3.99  sup_time_generating:                    0.
% 27.64/3.99  sup_time_sim_full:                      0.
% 27.64/3.99  sup_time_sim_immed:                     0.
% 27.64/3.99  
% 27.64/3.99  sup_num_of_clauses:                     6140
% 27.64/3.99  sup_num_in_active:                      348
% 27.64/3.99  sup_num_in_passive:                     5792
% 27.64/3.99  sup_num_of_loops:                       426
% 27.64/3.99  sup_fw_superposition:                   3849
% 27.64/3.99  sup_bw_superposition:                   5638
% 27.64/3.99  sup_immediate_simplified:               943
% 27.64/3.99  sup_given_eliminated:                   0
% 27.64/3.99  comparisons_done:                       0
% 27.64/3.99  comparisons_avoided:                    454
% 27.64/3.99  
% 27.64/3.99  ------ Simplifications
% 27.64/3.99  
% 27.64/3.99  
% 27.64/3.99  sim_fw_subset_subsumed:                 219
% 27.64/3.99  sim_bw_subset_subsumed:                 1684
% 27.64/3.99  sim_fw_subsumed:                        430
% 27.64/3.99  sim_bw_subsumed:                        16
% 27.64/3.99  sim_fw_subsumption_res:                 1
% 27.64/3.99  sim_bw_subsumption_res:                 0
% 27.64/3.99  sim_tautology_del:                      158
% 27.64/3.99  sim_eq_tautology_del:                   29
% 27.64/3.99  sim_eq_res_simp:                        0
% 27.64/3.99  sim_fw_demodulated:                     135
% 27.64/3.99  sim_bw_demodulated:                     31
% 27.64/3.99  sim_light_normalised:                   199
% 27.64/3.99  sim_joinable_taut:                      0
% 27.64/3.99  sim_joinable_simp:                      0
% 27.64/3.99  sim_ac_normalised:                      0
% 27.64/3.99  sim_smt_subsumption:                    0
% 27.64/3.99  
%------------------------------------------------------------------------------
